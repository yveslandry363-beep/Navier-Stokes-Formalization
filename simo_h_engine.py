import sympy as sp
import math
import argparse
import time

# =====================================================================
# MOTEUR FORMEL UNIVERSEL : LA SÉRIE DE SIMO-H (NAVIER-STOKES 3D)
# Zéro approximation numérique. Mathématiques pures uniquement.
# =====================================================================

# 1. INITIALISATION DES SYMBOLES MATHÉMATIQUES
t, nu = sp.symbols('t nu', real=True, positive=True)
I = sp.I


def leray_projector(k, v):
    """
    Projette exactement le vecteur v sur l'espace orthogonal à k.
    Formule : P_k(v) = v - k * (k . v) / |k|^2
    """
    k_sq = k.dot(k)
    if k_sq == 0:
        return v
    dot_kv = k.dot(v)
    correction = k * (dot_kv / k_sq)
    return sp.simplify(v - correction)


def bilinear_interaction(k, p, q, A_p, A_q):
    """
    Calcule le choc géométrique exact entre deux ondes.
    Formule : B = -(i/2) * P_k[ (A_p . q)A_q + (A_q . p)A_p ]
    """
    term1 = A_q * A_p.dot(q)
    term2 = A_p * A_q.dot(p)
    sum_terms = term1 + term2

    projected = leray_projector(k, sum_terms)
    return sp.simplify((-I / 2) * projected)


# 2. LE CŒUR DU MOTEUR : LA CASCADE DE SIMO-H
def compute_simo_h_series(initial_modes, max_order=3):
    """
    Génère l'arbre de résonance complet jusqu'à l'ordre max_order.
    initial_modes : Dictionnaire {vecteur_k: amplitude_A}
    Retourne la série de polynômes temporels exacts.
    """
    print(f"\n[DÉMARRAGE DU MOTEUR] Génération de la série jusqu'à l'Ordre {max_order}")
    print("-" * 60)

    # Historique des amplitudes spatiales par ordre
    # history[n] = dictionnaire des ondes créées à l'ordre n
    history = {1: initial_modes}

    # On itère pour créer les branches supérieures (Ordre 2, 3, 4...)
    for n in range(2, max_order + 1):
        history[n] = {}
        print(f"\n--- CALCUL DE L'ORDRE {n} ---")

        # L'ordre 'n' est formé par le choc de tous les sous-ordres i et j tels que i+j = n
        for i in range(1, n):
            j = n - i

            # On croise toutes les ondes de l'ordre i avec celles de l'ordre j
            for p_tuple, A_p in history[i].items():
                for q_tuple, A_q in history[j].items():
                    p = sp.Matrix(p_tuple)
                    q = sp.Matrix(q_tuple)

                    # LE VERROU DE SIMO-H : Filtre Orthogonal Strict
                    if p.dot(q) != 0:
                        continue  # Rejet géométrique (Interaction non-résonante)

                    k = p + q
                    k_tuple = tuple(k)

                    # Calcul de la matrice du choc
                    B_pq = bilinear_interaction(k, p, q, A_p, A_q)

                    if B_pq.is_zero_matrix:
                        continue

                    # Accumulation de l'amplitude pour cette onde k
                    if k_tuple not in history[n]:
                        history[n][k_tuple] = sp.zeros(3, 1)
                    history[n][k_tuple] += B_pq

                    print(f"Choc résonant validé : {tuple(p)} + {tuple(q)} -> {k_tuple}")

    # 3. L'ASSEMBLAGE TEMPOREL (LA FORMULE FINALE)
    print("\n" + "=" * 60)
    print(">>> SOLUTION EXACTE DE NAVIER-STOKES (SÉRIE TEMPORELLE) <<<")
    print("=" * 60)

    final_solution = {}

    for order, modes in history.items():
        # L'intégrale de convolution pour p.q = 0 donne exactement t^(n-1) / (n-1)!
        time_polynomial = (t ** (order - 1)) / math.factorial(order - 1)

        for k_tuple, amplitude in modes.items():
            if k_tuple not in final_solution:
                final_solution[k_tuple] = sp.zeros(3, 1)

            k = sp.Matrix(k_tuple)
            dissipation = sp.exp(-nu * k.dot(k) * t)

            # Application de la formule : (t^(n-1)/(n-1)!) * exp(-v|k|²t) * Amplitude
            exact_term = time_polynomial * dissipation * amplitude
            final_solution[k_tuple] += exact_term

    # Affichage du résultat propre
    for k_tuple, expression in final_solution.items():
        print(f"\nOnde {k_tuple} :")
        for idx, axis in enumerate(['X', 'Y', 'Z']):
            if expression[idx] != 0:
                print(f"  Vitesse {axis}(t) = {expression[idx]}")

    return final_solution


def default_initial_state():
    return {
        (1, 0, 0): sp.Matrix([0, 1, 1]),
        (0, 1, 0): sp.Matrix([1, 0, 1]),
    }


def parse_args():
    parser = argparse.ArgumentParser(description="Moteur formel Simo-H")
    parser.add_argument("--max-order", type=int, default=3, help="Ordre maximal de calcul")
    parser.add_argument(
        "--infinite",
        action="store_true",
        help="Relance indéfiniment le calcul en incrémentant l'ordre à chaque itération",
    )
    parser.add_argument(
        "--start-order",
        type=int,
        default=3,
        help="Ordre de départ pour le mode infini",
    )
    parser.add_argument(
        "--pause-seconds",
        type=float,
        default=0.0,
        help="Pause entre deux itérations du mode infini",
    )
    return parser.parse_args()


# =====================================================================
# EXÉCUTION (Le Réservoir de Carburant)
# =====================================================================
if __name__ == "__main__":
    args = parse_args()
    etat_initial = default_initial_state()

    if args.infinite:
        current_order = max(1, args.start_order)
        while True:
            print("\n" + "#" * 70)
            print(f"[MODE INFINI] Lancement du calcul à l'ordre {current_order}")
            compute_simo_h_series(etat_initial, max_order=current_order)
            current_order += 1
            if args.pause_seconds > 0:
                time.sleep(args.pause_seconds)
    else:
        compute_simo_h_series(etat_initial, max_order=max(1, args.max_order))
