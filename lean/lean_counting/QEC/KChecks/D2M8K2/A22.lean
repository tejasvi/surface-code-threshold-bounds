import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A21

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows7298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7298 = true := by
  rw [show D2M8K2.u7298 = KTree.node D2M8K2.u7294 (nat_lit 15403819) (nat_lit 1594385462) (nat_lit 0) D2M8K2.u7297 from rfl, allE_node, arows7294, irow7298, arows7297]
  all_goals rfl

theorem atot7298 : totK PD2M8K2 D2M8K2.u7298 = [0, 94445126902, 1059830158901, 2961853829600, 2640538976478, 530178448836, 19002749436, 0] := by
  rw [show D2M8K2.u7298 = KTree.node D2M8K2.u7294 (nat_lit 15403819) (nat_lit 1594385462) (nat_lit 0) D2M8K2.u7297 from rfl, totK_node, atot7294, atot7297]
  decide +kernel

theorem arows7305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7305 = true := by
  rw [show D2M8K2.u7305 = KTree.node D2M8K2.u7301 (nat_lit 15475739) (nat_lit 2901615284) (nat_lit 0) D2M8K2.u7304 from rfl, allE_node, arows7301, irow7305, arows7304]
  all_goals rfl

theorem atot7305 : totK PD2M8K2 D2M8K2.u7305 = [0, 778423203999, 2777789179450, 2863126753035, 835897371025, 46012320015, 0, 0] := by
  rw [show D2M8K2.u7305 = KTree.node D2M8K2.u7301 (nat_lit 15475739) (nat_lit 2901615284) (nat_lit 0) D2M8K2.u7304 from rfl, totK_node, atot7301, atot7304]
  decide +kernel

theorem arows7313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7313 = true := by
  rw [show D2M8K2.u7313 = KTree.node D2M8K2.u7309 (nat_lit 15482449) (nat_lit 1215164451) (nat_lit 0) D2M8K2.u7312 from rfl, allE_node, arows7309, irow7313, arows7312]
  all_goals rfl

theorem atot7313 : totK PD2M8K2 D2M8K2.u7313 = [0, 821956390626, 2976526861178, 2846758499232, 547263818343, 12643268820, 0, 0] := by
  rw [show D2M8K2.u7313 = KTree.node D2M8K2.u7309 (nat_lit 15482449) (nat_lit 1215164451) (nat_lit 0) D2M8K2.u7312 from rfl, totK_node, atot7309, atot7312]
  decide +kernel

theorem arows7320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7320 = true := by
  rw [show D2M8K2.u7320 = KTree.node D2M8K2.u7316 (nat_lit 15489065) (nat_lit 1440256510) (nat_lit 0) D2M8K2.u7319 from rfl, allE_node, arows7316, irow7320, arows7319]
  all_goals rfl

theorem atot7320 : totK PD2M8K2 D2M8K2.u7320 = [0, 422883574688, 1993673350632, 3050955047282, 1523451350913, 257333386030, 21385604922, 0] := by
  rw [show D2M8K2.u7320 = KTree.node D2M8K2.u7316 (nat_lit 15489065) (nat_lit 1440256510) (nat_lit 0) D2M8K2.u7319 from rfl, totK_node, atot7316, atot7319]
  decide +kernel

theorem arows7329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7329 = true := by
  rw [show D2M8K2.u7329 = KTree.node D2M8K2.u7325 (nat_lit 15498555) (nat_lit 2576793159) (nat_lit 0) D2M8K2.u7328 from rfl, allE_node, arows7325, irow7329, arows7328]
  all_goals rfl

theorem atot7329 : totK PD2M8K2 D2M8K2.u7329 = [0, 0, 823962568562, 2923869548719, 2804147474368, 653121221696, 20696137567, 0] := by
  rw [show D2M8K2.u7329 = KTree.node D2M8K2.u7325 (nat_lit 15498555) (nat_lit 2576793159) (nat_lit 0) D2M8K2.u7328 from rfl, totK_node, atot7325, atot7328]
  decide +kernel

theorem arows7336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7336 = true := by
  rw [show D2M8K2.u7336 = KTree.node D2M8K2.u7332 (nat_lit 15505985) (nat_lit 2222625568) (nat_lit 0) D2M8K2.u7335 from rfl, allE_node, arows7332, irow7336, arows7335]
  all_goals rfl

theorem atot7336 : totK PD2M8K2 D2M8K2.u7336 = [0, 0, 836605716536, 3061454185535, 2817299820658, 482027833404, 7872688237, 0] := by
  rw [show D2M8K2.u7336 = KTree.node D2M8K2.u7332 (nat_lit 15505985) (nat_lit 2222625568) (nat_lit 0) D2M8K2.u7335 from rfl, totK_node, atot7332, atot7335]
  decide +kernel

theorem arows7344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7344 = true := by
  rw [show D2M8K2.u7344 = KTree.node D2M8K2.u7340 (nat_lit 15514370) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u7343 from rfl, allE_node, arows7340, irow7344, arows7343]
  all_goals rfl

theorem atot7344 : totK PD2M8K2 D2M8K2.u7344 = [0, 772057274113, 2657208464809, 2611930663071, 1001280404768, 202154822884, 8063697217, 0] := by
  rw [show D2M8K2.u7344 = KTree.node D2M8K2.u7340 (nat_lit 15514370) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u7343 from rfl, totK_node, atot7340, atot7343]
  decide +kernel

theorem arows7351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7351 = true := by
  rw [show D2M8K2.u7351 = KTree.node D2M8K2.u7347 (nat_lit 15519939) (nat_lit 2942356659) (nat_lit 0) D2M8K2.u7350 from rfl, allE_node, arows7347, irow7351, arows7350]
  all_goals rfl

theorem atot7351 : totK PD2M8K2 D2M8K2.u7351 = [0, 853173737057, 2957230764732, 2792416846940, 623529886028, 22356163970, 0, 0] := by
  rw [show D2M8K2.u7351 = KTree.node D2M8K2.u7347 (nat_lit 15519939) (nat_lit 2942356659) (nat_lit 0) D2M8K2.u7350 from rfl, totK_node, atot7347, atot7350]
  decide +kernel

theorem arows7361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7361 = true := by
  rw [show D2M8K2.u7361 = KTree.node D2M8K2.u7357 (nat_lit 15530304) (nat_lit 3287641892) (nat_lit 0) D2M8K2.u7360 from rfl, allE_node, arows7357, irow7361, arows7360]
  all_goals rfl

theorem atot7361 : totK PD2M8K2 D2M8K2.u7361 = [0, 417115925447, 2219348126058, 3293066077628, 1220272879630, 76114654496, 0, 0] := by
  rw [show D2M8K2.u7361 = KTree.node D2M8K2.u7357 (nat_lit 15530304) (nat_lit 3287641892) (nat_lit 0) D2M8K2.u7360 from rfl, totK_node, atot7357, atot7360]
  decide +kernel

theorem arows7368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7368 = true := by
  rw [show D2M8K2.u7368 = KTree.node D2M8K2.u7364 (nat_lit 15540245) (nat_lit 2387674188) (nat_lit 0) D2M8K2.u7367 from rfl, allE_node, arows7364, irow7368, arows7367]
  all_goals rfl

theorem atot7368 : totK PD2M8K2 D2M8K2.u7368 = [0, 0, 1042914377731, 3283763959619, 2388711060066, 403166671504, 14037798012, 0] := by
  rw [show D2M8K2.u7368 = KTree.node D2M8K2.u7364 (nat_lit 15540245) (nat_lit 2387674188) (nat_lit 0) D2M8K2.u7367 from rfl, totK_node, atot7364, atot7367]
  decide +kernel

theorem arows7376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7376 = true := by
  rw [show D2M8K2.u7376 = KTree.node D2M8K2.u7372 (nat_lit 15556226) (nat_lit 4054250822) (nat_lit 0) D2M8K2.u7375 from rfl, allE_node, arows7372, irow7376, arows7375]
  all_goals rfl

theorem atot7376 : totK PD2M8K2 D2M8K2.u7376 = [0, 466138187239, 2002784508788, 3023541272546, 1564844976964, 173734344365, 3552795014, 0] := by
  rw [show D2M8K2.u7376 = KTree.node D2M8K2.u7372 (nat_lit 15556226) (nat_lit 4054250822) (nat_lit 0) D2M8K2.u7375 from rfl, totK_node, atot7372, atot7375]
  decide +kernel

theorem arows7383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7383 = true := by
  rw [show D2M8K2.u7383 = KTree.node D2M8K2.u7379 (nat_lit 15565619) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u7382 from rfl, allE_node, arows7379, irow7383, arows7382]
  all_goals rfl

theorem atot7383 : totK PD2M8K2 D2M8K2.u7383 = [0, 858414692318, 3036500309413, 2767858803481, 546563438225, 17134695116, 0, 0] := by
  rw [show D2M8K2.u7383 = KTree.node D2M8K2.u7379 (nat_lit 15565619) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u7382 from rfl, totK_node, atot7379, atot7382]
  decide +kernel

theorem arows7392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7392 = true := by
  rw [show D2M8K2.u7392 = KTree.node D2M8K2.u7388 (nat_lit 15576548) (nat_lit 3225891353) (nat_lit 0) D2M8K2.u7391 from rfl, allE_node, arows7388, irow7392, arows7391]
  all_goals rfl

theorem atot7392 : totK PD2M8K2 D2M8K2.u7392 = [0, 337788462646, 2055922423904, 3373882768222, 1419985115689, 93311885561, 0, 0] := by
  rw [show D2M8K2.u7392 = KTree.node D2M8K2.u7388 (nat_lit 15576548) (nat_lit 3225891353) (nat_lit 0) D2M8K2.u7391 from rfl, totK_node, atot7388, atot7391]
  decide +kernel

theorem arows7399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7399 = true := by
  rw [show D2M8K2.u7399 = KTree.node D2M8K2.u7395 (nat_lit 15587826) (nat_lit 3444910579) (nat_lit 0) D2M8K2.u7398 from rfl, allE_node, arows7395, irow7399, arows7398]
  all_goals rfl

theorem atot7399 : totK PD2M8K2 D2M8K2.u7399 = [0, 85146215446, 1038971355531, 3145918730920, 2516377680836, 368658104138, 7133208874, 0] := by
  rw [show D2M8K2.u7399 = KTree.node D2M8K2.u7395 (nat_lit 15587826) (nat_lit 3444910579) (nat_lit 0) D2M8K2.u7398 from rfl, totK_node, atot7395, atot7398]
  decide +kernel

theorem arows7407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7407 = true := by
  rw [show D2M8K2.u7407 = KTree.node D2M8K2.u7403 (nat_lit 15598040) (nat_lit 3866861740) (nat_lit 0) D2M8K2.u7406 from rfl, allE_node, arows7403, irow7407, arows7406]
  all_goals rfl

theorem atot7407 : totK PD2M8K2 D2M8K2.u7407 = [0, 833412148826, 2879849163080, 2737208123586, 747219241732, 38970858654, 0, 0] := by
  rw [show D2M8K2.u7407 = KTree.node D2M8K2.u7403 (nat_lit 15598040) (nat_lit 3866861740) (nat_lit 0) D2M8K2.u7406 from rfl, totK_node, atot7403, atot7406]
  decide +kernel

theorem arows7414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7414 = true := by
  rw [show D2M8K2.u7414 = KTree.node D2M8K2.u7410 (nat_lit 15604315) (nat_lit 1705291116) (nat_lit 0) D2M8K2.u7413 from rfl, allE_node, arows7410, irow7414, arows7413]
  all_goals rfl

theorem atot7414 : totK PD2M8K2 D2M8K2.u7414 = [0, 803180070864, 2912551788470, 2835522182867, 629507555867, 25102339103, 0, 0] := by
  rw [show D2M8K2.u7414 = KTree.node D2M8K2.u7410 (nat_lit 15604315) (nat_lit 1705291116) (nat_lit 0) D2M8K2.u7413 from rfl, totK_node, atot7410, atot7413]
  decide +kernel

theorem arows7426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7426 = true := by
  rw [show D2M8K2.u7426 = KTree.node D2M8K2.u7422 (nat_lit 15615083) (nat_lit 2253823115) (nat_lit 32) D2M8K2.u7425 from rfl, allE_node, arows7422, irow7426, arows7425]
  all_goals rfl

theorem atot7426 : totK PD2M8K2 D2M8K2.u7426 = [0, 265686162196, 2025051307672, 3487472022149, 1338949076288, 79298058921, 0, 0] := by
  rw [show D2M8K2.u7426 = KTree.node D2M8K2.u7422 (nat_lit 15615083) (nat_lit 2253823115) (nat_lit 32) D2M8K2.u7425 from rfl, totK_node, atot7422, atot7425]
  decide +kernel

theorem arows7433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7433 = true := by
  rw [show D2M8K2.u7433 = KTree.node D2M8K2.u7429 (nat_lit 15628422) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u7432 from rfl, allE_node, arows7429, irow7433, arows7432]
  all_goals rfl

theorem atot7433 : totK PD2M8K2 D2M8K2.u7433 = [0, 169606407816, 1416194867537, 3252006244122, 2032448844153, 263491193460, 4977114383, 0] := by
  rw [show D2M8K2.u7433 = KTree.node D2M8K2.u7429 (nat_lit 15628422) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u7432 from rfl, totK_node, atot7429, atot7432]
  decide +kernel

theorem arows7441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7441 = true := by
  rw [show D2M8K2.u7441 = KTree.node D2M8K2.u7437 (nat_lit 15639752) (nat_lit 3731389844) (nat_lit 0) D2M8K2.u7440 from rfl, allE_node, arows7437, irow7441, arows7440]
  all_goals rfl

theorem atot7441 : totK PD2M8K2 D2M8K2.u7441 = [0, 805565840657, 2838285703917, 2847778711671, 765902558258, 38958597222, 0, 0] := by
  rw [show D2M8K2.u7441 = KTree.node D2M8K2.u7437 (nat_lit 15639752) (nat_lit 3731389844) (nat_lit 0) D2M8K2.u7440 from rfl, totK_node, atot7437, atot7440]
  decide +kernel

theorem arows7448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7448 = true := by
  rw [show D2M8K2.u7448 = KTree.node D2M8K2.u7444 (nat_lit 15646262) (nat_lit 3968625444) (nat_lit 0) D2M8K2.u7447 from rfl, allE_node, arows7444, irow7448, arows7447]
  all_goals rfl

theorem atot7448 : totK PD2M8K2 D2M8K2.u7448 = [0, 839951816754, 2955739188016, 2827746532886, 624513427605, 21635480846, 0, 0] := by
  rw [show D2M8K2.u7448 = KTree.node D2M8K2.u7444 (nat_lit 15646262) (nat_lit 3968625444) (nat_lit 0) D2M8K2.u7447 from rfl, totK_node, atot7444, atot7447]
  decide +kernel

theorem arows7457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7457 = true := by
  rw [show D2M8K2.u7457 = KTree.node D2M8K2.u7453 (nat_lit 15656404) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u7456 from rfl, allE_node, arows7453, irow7457, arows7456]
  all_goals rfl

theorem atot7457 : totK PD2M8K2 D2M8K2.u7457 = [0, 180187839875, 1633781418354, 3376332885190, 1843189489827, 173071902801, 1310285577, 0] := by
  rw [show D2M8K2.u7457 = KTree.node D2M8K2.u7453 (nat_lit 15656404) (nat_lit 3765632296) (nat_lit 0) D2M8K2.u7456 from rfl, totK_node, atot7453, atot7456]
  decide +kernel

theorem arows7464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7464 = true := by
  rw [show D2M8K2.u7464 = KTree.node D2M8K2.u7460 (nat_lit 15665588) (nat_lit 3440650200) (nat_lit 0) D2M8K2.u7463 from rfl, allE_node, arows7460, irow7464, arows7463]
  all_goals rfl

theorem atot7464 : totK PD2M8K2 D2M8K2.u7464 = [0, 0, 1002670165890, 3294367763172, 2565984103418, 369674226496, 6324401156, 0] := by
  rw [show D2M8K2.u7464 = KTree.node D2M8K2.u7460 (nat_lit 15665588) (nat_lit 3440650200) (nat_lit 0) D2M8K2.u7463 from rfl, totK_node, atot7460, atot7463]
  decide +kernel

theorem arows7472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7472 = true := by
  rw [show D2M8K2.u7472 = KTree.node D2M8K2.u7468 (nat_lit 15925308) (nat_lit 3255558676) (nat_lit 0) D2M8K2.u7471 from rfl, allE_node, arows7468, irow7472, arows7471]
  all_goals rfl

theorem atot7472 : totK PD2M8K2 D2M8K2.u7472 = [0, 523189548123, 2000734545362, 2621314485009, 1638641977320, 393935334904, 18014152641, 0] := by
  rw [show D2M8K2.u7472 = KTree.node D2M8K2.u7468 (nat_lit 15925308) (nat_lit 3255558676) (nat_lit 0) D2M8K2.u7471 from rfl, totK_node, atot7468, atot7471]
  decide +kernel

theorem arows7479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7479 = true := by
  rw [show D2M8K2.u7479 = KTree.node D2M8K2.u7475 (nat_lit 15935684) (nat_lit 3197948873) (nat_lit 0) D2M8K2.u7478 from rfl, allE_node, arows7475, irow7479, arows7478]
  all_goals rfl

theorem atot7479 : totK PD2M8K2 D2M8K2.u7479 = [0, 902161336156, 3030799552957, 2679902521851, 535284183629, 17829750455, 0, 0] := by
  rw [show D2M8K2.u7479 = KTree.node D2M8K2.u7475 (nat_lit 15935684) (nat_lit 3197948873) (nat_lit 0) D2M8K2.u7478 from rfl, totK_node, atot7475, atot7478]
  decide +kernel

theorem arows7489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7489 = true := by
  rw [show D2M8K2.u7489 = KTree.node D2M8K2.u7485 (nat_lit 15943349) (nat_lit 2304042884) (nat_lit 0) D2M8K2.u7488 from rfl, allE_node, arows7485, irow7489, arows7488]
  all_goals rfl

theorem atot7489 : totK PD2M8K2 D2M8K2.u7489 = [0, 580298837745, 2590344807132, 3098594063786, 832837847717, 32143479695, 0, 0] := by
  rw [show D2M8K2.u7489 = KTree.node D2M8K2.u7485 (nat_lit 15943349) (nat_lit 2304042884) (nat_lit 0) D2M8K2.u7488 from rfl, totK_node, atot7485, atot7488]
  decide +kernel

theorem arows7496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7496 = true := by
  rw [show D2M8K2.u7496 = KTree.node D2M8K2.u7492 (nat_lit 15953730) (nat_lit 1365148086) (nat_lit 0) D2M8K2.u7495 from rfl, allE_node, arows7492, irow7496, arows7495]
  all_goals rfl

theorem atot7496 : totK PD2M8K2 D2M8K2.u7496 = [0, 0, 1254495274615, 3586208483871, 2010477593120, 179434543695, 1369150432, 0] := by
  rw [show D2M8K2.u7496 = KTree.node D2M8K2.u7492 (nat_lit 15953730) (nat_lit 1365148086) (nat_lit 0) D2M8K2.u7495 from rfl, totK_node, atot7492, atot7495]
  decide +kernel

theorem arows7504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7504 = true := by
  rw [show D2M8K2.u7504 = KTree.node D2M8K2.u7500 (nat_lit 15971001) (nat_lit 1871988145) (nat_lit 0) D2M8K2.u7503 from rfl, allE_node, arows7500, irow7504, arows7503]
  all_goals rfl

theorem atot7504 : totK PD2M8K2 D2M8K2.u7504 = [0, 497427585932, 2214000476737, 3199202584605, 1277815965806, 67597511576, 0, 0] := by
  rw [show D2M8K2.u7504 = KTree.node D2M8K2.u7500 (nat_lit 15971001) (nat_lit 1871988145) (nat_lit 0) D2M8K2.u7503 from rfl, totK_node, atot7500, atot7503]
  decide +kernel

theorem arows7511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7511 = true := by
  rw [show D2M8K2.u7511 = KTree.node D2M8K2.u7507 (nat_lit 15976934) (nat_lit 3974640573) (nat_lit 0) D2M8K2.u7510 from rfl, allE_node, arows7507, irow7511, arows7510]
  all_goals rfl

theorem atot7511 : totK PD2M8K2 D2M8K2.u7511 = [0, 859055998432, 2999661620547, 2814931989509, 594396650043, 20061829716, 0, 0] := by
  rw [show D2M8K2.u7511 = KTree.node D2M8K2.u7507 (nat_lit 15976934) (nat_lit 3974640573) (nat_lit 0) D2M8K2.u7510 from rfl, totK_node, atot7507, atot7510]
  decide +kernel

theorem arows7520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7520 = true := by
  rw [show D2M8K2.u7520 = KTree.node D2M8K2.u7516 (nat_lit 15984627) (nat_lit 3653736964) (nat_lit 0) D2M8K2.u7519 from rfl, allE_node, arows7516, irow7520, arows7519]
  all_goals rfl

theorem atot7520 : totK PD2M8K2 D2M8K2.u7520 = [0, 672400669610, 2701507993219, 2998850542730, 836694956541, 47570537026, 0, 0] := by
  rw [show D2M8K2.u7520 = KTree.node D2M8K2.u7516 (nat_lit 15984627) (nat_lit 3653736964) (nat_lit 0) D2M8K2.u7519 from rfl, totK_node, atot7516, atot7519]
  decide +kernel

theorem arows7527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7527 = true := by
  rw [show D2M8K2.u7527 = KTree.node D2M8K2.u7523 (nat_lit 15994495) (nat_lit 1600866443) (nat_lit 0) D2M8K2.u7526 from rfl, allE_node, arows7523, irow7527, arows7526]
  all_goals rfl

theorem atot7527 : totK PD2M8K2 D2M8K2.u7527 = [0, 0, 819590237823, 2913490427250, 2806533241816, 678721042304, 29441591382, 0] := by
  rw [show D2M8K2.u7527 = KTree.node D2M8K2.u7523 (nat_lit 15994495) (nat_lit 1600866443) (nat_lit 0) D2M8K2.u7526 from rfl, totK_node, atot7523, atot7526]
  decide +kernel

theorem arows7535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7535 = true := by
  rw [show D2M8K2.u7535 = KTree.node D2M8K2.u7531 (nat_lit 16003124) (nat_lit 3417883736) (nat_lit 0) D2M8K2.u7534 from rfl, allE_node, arows7531, irow7535, arows7534]
  all_goals rfl

theorem atot7535 : totK PD2M8K2 D2M8K2.u7535 = [0, 0, 1064623415557, 3423838544368, 2483465688640, 281278490883, 1415142070, 0] := by
  rw [show D2M8K2.u7535 = KTree.node D2M8K2.u7531 (nat_lit 16003124) (nat_lit 3417883736) (nat_lit 0) D2M8K2.u7534 from rfl, totK_node, atot7531, atot7534]
  decide +kernel

theorem arows7542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7542 = true := by
  rw [show D2M8K2.u7542 = KTree.node D2M8K2.u7538 (nat_lit 16010881) (nat_lit 1480340801) (nat_lit 0) D2M8K2.u7541 from rfl, allE_node, arows7538, irow7542, arows7541]
  all_goals rfl

theorem atot7542 : totK PD2M8K2 D2M8K2.u7542 = [0, 843193660764, 2754402496743, 2507782365325, 923672377564, 193589349210, 5510671013, 0] := by
  rw [show D2M8K2.u7542 = KTree.node D2M8K2.u7538 (nat_lit 16010881) (nat_lit 1480340801) (nat_lit 0) D2M8K2.u7541 from rfl, totK_node, atot7538, atot7541]
  decide +kernel

theorem arows7553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7553 = true := by
  rw [show D2M8K2.u7553 = KTree.node D2M8K2.u7549 (nat_lit 16016975) (nat_lit 2183188888) (nat_lit 0) D2M8K2.u7552 from rfl, allE_node, arows7549, irow7553, arows7552]
  all_goals rfl

theorem atot7553 : totK PD2M8K2 D2M8K2.u7553 = [0, 866062887121, 2927442669356, 2767222060541, 679062027951, 23204656041, 0, 0] := by
  rw [show D2M8K2.u7553 = KTree.node D2M8K2.u7549 (nat_lit 16016975) (nat_lit 2183188888) (nat_lit 0) D2M8K2.u7552 from rfl, totK_node, atot7549, atot7552]
  decide +kernel

theorem arows7560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7560 = true := by
  rw [show D2M8K2.u7560 = KTree.node D2M8K2.u7556 (nat_lit 16027282) (nat_lit 3878653370) (nat_lit 0) D2M8K2.u7559 from rfl, allE_node, arows7556, irow7560, arows7559]
  all_goals rfl

theorem atot7560 : totK PD2M8K2 D2M8K2.u7560 = [0, 423750883410, 2307328621510, 3352204090311, 1042233715941, 41119083076, 0, 0] := by
  rw [show D2M8K2.u7560 = KTree.node D2M8K2.u7556 (nat_lit 16027282) (nat_lit 3878653370) (nat_lit 0) D2M8K2.u7559 from rfl, totK_node, atot7556, atot7559]
  decide +kernel

theorem arows7568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7568 = true := by
  rw [show D2M8K2.u7568 = KTree.node D2M8K2.u7564 (nat_lit 16035990) (nat_lit 3354405407) (nat_lit 0) D2M8K2.u7567 from rfl, allE_node, arows7564, irow7568, arows7567]
  all_goals rfl

theorem atot7568 : totK PD2M8K2 D2M8K2.u7568 = [0, 0, 905426735255, 3127692504949, 2635386555986, 456539891373, 14222663156, 0] := by
  rw [show D2M8K2.u7568 = KTree.node D2M8K2.u7564 (nat_lit 16035990) (nat_lit 3354405407) (nat_lit 0) D2M8K2.u7567 from rfl, totK_node, atot7564, atot7567]
  decide +kernel

theorem arows7575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7575 = true := by
  rw [show D2M8K2.u7575 = KTree.node D2M8K2.u7571 (nat_lit 16046457) (nat_lit 1764752514) (nat_lit 0) D2M8K2.u7574 from rfl, allE_node, arows7571, irow7575, arows7574]
  all_goals rfl

theorem atot7575 : totK PD2M8K2 D2M8K2.u7575 = [0, 406174846124, 1785101755292, 2934301726490, 1738492699656, 216557260387, 4574395652, 0] := by
  rw [show D2M8K2.u7575 = KTree.node D2M8K2.u7571 (nat_lit 16046457) (nat_lit 1764752514) (nat_lit 0) D2M8K2.u7574 from rfl, totK_node, atot7571, atot7574]
  decide +kernel

theorem arows7584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7584 = true := by
  rw [show D2M8K2.u7584 = KTree.node D2M8K2.u7580 (nat_lit 16096680) (nat_lit 2475995363) (nat_lit 0) D2M8K2.u7583 from rfl, allE_node, arows7580, irow7584, arows7583]
  all_goals rfl

theorem atot7584 : totK PD2M8K2 D2M8K2.u7584 = [0, 771334680789, 2811987090230, 2864096057604, 771756983369, 37270810824, 0, 0] := by
  rw [show D2M8K2.u7584 = KTree.node D2M8K2.u7580 (nat_lit 16096680) (nat_lit 2475995363) (nat_lit 0) D2M8K2.u7583 from rfl, totK_node, atot7580, atot7583]
  decide +kernel

theorem arows7591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7591 = true := by
  rw [show D2M8K2.u7591 = KTree.node D2M8K2.u7587 (nat_lit 16102899) (nat_lit 2986295984) (nat_lit 0) D2M8K2.u7590 from rfl, allE_node, arows7587, irow7591, arows7590]
  all_goals rfl

theorem atot7591 : totK PD2M8K2 D2M8K2.u7591 = [0, 833997639955, 2989467891715, 2789445645158, 555139996374, 17829750455, 0, 0] := by
  rw [show D2M8K2.u7591 = KTree.node D2M8K2.u7587 (nat_lit 16102899) (nat_lit 2986295984) (nat_lit 0) D2M8K2.u7590 from rfl, totK_node, atot7587, atot7590]
  decide +kernel

theorem arows7599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7599 = true := by
  rw [show D2M8K2.u7599 = KTree.node D2M8K2.u7595 (nat_lit 16114233) (nat_lit 1835229511) (nat_lit 0) D2M8K2.u7598 from rfl, allE_node, arows7595, irow7599, arows7598]
  all_goals rfl

theorem atot7599 : totK PD2M8K2 D2M8K2.u7599 = [0, 0, 1397718433921, 3689566800292, 1882383788154, 148641628362, 1138244013, 0] := by
  rw [show D2M8K2.u7599 = KTree.node D2M8K2.u7595 (nat_lit 16114233) (nat_lit 1835229511) (nat_lit 0) D2M8K2.u7598 from rfl, totK_node, atot7595, atot7598]
  decide +kernel

theorem arows7606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7606 = true := by
  rw [show D2M8K2.u7606 = KTree.node D2M8K2.u7602 (nat_lit 16126371) (nat_lit 3644560346) (nat_lit 0) D2M8K2.u7605 from rfl, allE_node, arows7602, irow7606, arows7605]
  all_goals rfl

theorem atot7606 : totK PD2M8K2 D2M8K2.u7606 = [0, 252651705119, 1559386816067, 3155583105908, 1885874643254, 226139129787, 4977114383, 0] := by
  rw [show D2M8K2.u7606 = KTree.node D2M8K2.u7602 (nat_lit 16126371) (nat_lit 3644560346) (nat_lit 0) D2M8K2.u7605 from rfl, totK_node, atot7602, atot7605]
  decide +kernel

theorem arows7616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7616 = true := by
  rw [show D2M8K2.u7616 = KTree.node D2M8K2.u7612 (nat_lit 16137298) (nat_lit 3155563560) (nat_lit 0) D2M8K2.u7615 from rfl, allE_node, arows7612, irow7616, arows7615]
  all_goals rfl

theorem atot7616 : totK PD2M8K2 D2M8K2.u7616 = [0, 764946038579, 2798686519761, 2886719673421, 773046521669, 37377293004, 0, 0] := by
  rw [show D2M8K2.u7616 = KTree.node D2M8K2.u7612 (nat_lit 16137298) (nat_lit 3155563560) (nat_lit 0) D2M8K2.u7615 from rfl, totK_node, atot7612, atot7615]
  decide +kernel

theorem arows7623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7623 = true := by
  rw [show D2M8K2.u7623 = KTree.node D2M8K2.u7619 (nat_lit 16143508) (nat_lit 3089809520) (nat_lit 0) D2M8K2.u7622 from rfl, allE_node, arows7619, irow7623, arows7622]
  all_goals rfl

theorem atot7623 : totK PD2M8K2 D2M8K2.u7623 = [0, 910855539203, 3021652538901, 2740910714289, 574400915792, 18499430880, 0, 0] := by
  rw [show D2M8K2.u7623 = KTree.node D2M8K2.u7619 (nat_lit 16143508) (nat_lit 3089809520) (nat_lit 0) D2M8K2.u7622 from rfl, totK_node, atot7619, atot7622]
  decide +kernel

theorem arows7631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7631 = true := by
  rw [show D2M8K2.u7631 = KTree.node D2M8K2.u7627 (nat_lit 16154353) (nat_lit 1534913353) (nat_lit 0) D2M8K2.u7630 from rfl, allE_node, arows7627, irow7631, arows7630]
  all_goals rfl

theorem atot7631 : totK PD2M8K2 D2M8K2.u7631 = [0, 93763323609, 1504241166299, 3467384670903, 1928560300095, 167676153873, 1310285577, 0] := by
  rw [show D2M8K2.u7631 = KTree.node D2M8K2.u7627 (nat_lit 16154353) (nat_lit 1534913353) (nat_lit 0) D2M8K2.u7630 from rfl, totK_node, atot7627, atot7630]
  decide +kernel

theorem arows7638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7638 = true := by
  rw [show D2M8K2.u7638 = KTree.node D2M8K2.u7634 (nat_lit 16162809) (nat_lit 1626849707) (nat_lit 0) D2M8K2.u7637 from rfl, allE_node, arows7634, irow7638, arows7637]
  all_goals rfl

theorem atot7638 : totK PD2M8K2 D2M8K2.u7638 = [0, 0, 1186919709664, 3423582124228, 2312470896766, 288859190364, 4879840392, 0] := by
  rw [show D2M8K2.u7638 = KTree.node D2M8K2.u7634 (nat_lit 16162809) (nat_lit 1626849707) (nat_lit 0) D2M8K2.u7637 from rfl, totK_node, atot7634, atot7637]
  decide +kernel

theorem arows7647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7647 = true := by
  rw [show D2M8K2.u7647 = KTree.node D2M8K2.u7643 (nat_lit 16175288) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u7646 from rfl, allE_node, arows7643, irow7647, arows7646]
  all_goals rfl

theorem atot7647 : totK PD2M8K2 D2M8K2.u7647 = [0, 0, 865066104229, 3087899239836, 2716399623648, 474091746793, 15155644480, 0] := by
  rw [show D2M8K2.u7647 = KTree.node D2M8K2.u7643 (nat_lit 16175288) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u7646 from rfl, totK_node, atot7643, atot7646]
  decide +kernel

theorem arows7654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7654 = true := by
  rw [show D2M8K2.u7654 = KTree.node D2M8K2.u7650 (nat_lit 16186107) (nat_lit 1914957179) (nat_lit 40) D2M8K2.u7653 from rfl, allE_node, arows7650, irow7654, arows7653]
  all_goals rfl

theorem atot7654 : totK PD2M8K2 D2M8K2.u7654 = [0, 0, 813537518329, 3034363849223, 2715973624454, 471432694617, 15344305730, 0] := by
  rw [show D2M8K2.u7654 = KTree.node D2M8K2.u7650 (nat_lit 16186107) (nat_lit 1914957179) (nat_lit 40) D2M8K2.u7653 from rfl, totK_node, atot7650, atot7653]
  decide +kernel

theorem arows7662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7662 = true := by
  rw [show D2M8K2.u7662 = KTree.node D2M8K2.u7658 (nat_lit 16193933) (nat_lit 1930111016) (nat_lit 0) D2M8K2.u7661 from rfl, allE_node, arows7658, irow7662, arows7661]
  all_goals rfl

theorem atot7662 : totK PD2M8K2 D2M8K2.u7662 = [0, 0, 411769882097, 2062659020111, 3133570512276, 1293386395672, 126024433067, 1275377855] := by
  rw [show D2M8K2.u7662 = KTree.node D2M8K2.u7658 (nat_lit 16193933) (nat_lit 1930111016) (nat_lit 0) D2M8K2.u7661 from rfl, totK_node, atot7658, atot7661]
  decide +kernel

theorem arows7669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7669 = true := by
  rw [show D2M8K2.u7669 = KTree.node D2M8K2.u7665 (nat_lit 16208863) (nat_lit 1436544655) (nat_lit 640) D2M8K2.u7668 from rfl, allE_node, arows7665, irow7669, arows7668]
  all_goals rfl

theorem atot7669 : totK PD2M8K2 D2M8K2.u7669 = [0, 0, 94308027437, 1785119834875, 3747628914480, 1356976305950, 66579953067, 0] := by
  rw [show D2M8K2.u7669 = KTree.node D2M8K2.u7665 (nat_lit 16208863) (nat_lit 1436544655) (nat_lit 640) D2M8K2.u7668 from rfl, totK_node, atot7665, atot7668]
  decide +kernel

theorem arows7682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7682 = true := by
  rw [show D2M8K2.u7682 = KTree.node D2M8K2.u7678 (nat_lit 16222520) (nat_lit 3666032004) (nat_lit 0) D2M8K2.u7681 from rfl, allE_node, arows7678, irow7682, arows7681]
  all_goals rfl

theorem atot7682 : totK PD2M8K2 D2M8K2.u7682 = [0, 0, 809497931403, 2900571320109, 2872942251690, 685505049401, 34435583994, 0] := by
  rw [show D2M8K2.u7682 = KTree.node D2M8K2.u7678 (nat_lit 16222520) (nat_lit 3666032004) (nat_lit 0) D2M8K2.u7681 from rfl, totK_node, atot7678, atot7681]
  decide +kernel

theorem arows7689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7689 = true := by
  rw [show D2M8K2.u7689 = KTree.node D2M8K2.u7685 (nat_lit 16231473) (nat_lit 1834627468) (nat_lit 0) D2M8K2.u7688 from rfl, allE_node, arows7685, irow7689, arows7688]
  all_goals rfl

theorem atot7689 : totK PD2M8K2 D2M8K2.u7689 = [0, 0, 1117737313696, 3436502310161, 2447215495752, 312083754989, 3845941866, 0] := by
  rw [show D2M8K2.u7689 = KTree.node D2M8K2.u7685 (nat_lit 16231473) (nat_lit 1834627468) (nat_lit 0) D2M8K2.u7688 from rfl, totK_node, atot7685, atot7688]
  decide +kernel

theorem arows7697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7697 = true := by
  rw [show D2M8K2.u7697 = KTree.node D2M8K2.u7693 (nat_lit 16259962) (nat_lit 2753124640) (nat_lit 0) D2M8K2.u7696 from rfl, allE_node, arows7693, irow7697, arows7696]
  all_goals rfl

theorem atot7697 : totK PD2M8K2 D2M8K2.u7697 = [0, 0, 837545671150, 2992134022180, 2732685055328, 598028087004, 31470292849, 0] := by
  rw [show D2M8K2.u7697 = KTree.node D2M8K2.u7693 (nat_lit 16259962) (nat_lit 2753124640) (nat_lit 0) D2M8K2.u7696 from rfl, totK_node, atot7693, atot7696]
  decide +kernel

theorem arows7704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7704 = true := by
  rw [show D2M8K2.u7704 = KTree.node D2M8K2.u7700 (nat_lit 16266310) (nat_lit 3728482711) (nat_lit 0) D2M8K2.u7703 from rfl, allE_node, arows7700, irow7704, arows7703]
  all_goals rfl

theorem atot7704 : totK PD2M8K2 D2M8K2.u7704 = [0, 0, 861894085028, 2941973849691, 2769443632356, 593466661141, 19634548335, 0] := by
  rw [show D2M8K2.u7704 = KTree.node D2M8K2.u7700 (nat_lit 16266310) (nat_lit 3728482711) (nat_lit 0) D2M8K2.u7703 from rfl, totK_node, atot7700, atot7703]
  decide +kernel

theorem arows7713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7713 = true := by
  rw [show D2M8K2.u7713 = KTree.node D2M8K2.u7709 (nat_lit 16276670) (nat_lit 3861145161) (nat_lit 0) D2M8K2.u7712 from rfl, allE_node, arows7709, irow7713, arows7712]
  all_goals rfl

theorem atot7713 : totK PD2M8K2 D2M8K2.u7713 = [0, 0, 420582282504, 2113026938781, 3144623341687, 1254640032427, 118290746584, 1206465782] := by
  rw [show D2M8K2.u7713 = KTree.node D2M8K2.u7709 (nat_lit 16276670) (nat_lit 3861145161) (nat_lit 0) D2M8K2.u7712 from rfl, totK_node, atot7709, atot7712]
  decide +kernel

theorem arows7720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7720 = true := by
  rw [show D2M8K2.u7720 = KTree.node D2M8K2.u7716 (nat_lit 16285876) (nat_lit 4012785417) (nat_lit 0) D2M8K2.u7719 from rfl, allE_node, arows7716, irow7720, arows7719]
  all_goals rfl

theorem atot7720 : totK PD2M8K2 D2M8K2.u7720 = [0, 0, 0, 1122358806648, 3303701360762, 2284308540634, 371764388945, 13016197374] := by
  rw [show D2M8K2.u7720 = KTree.node D2M8K2.u7716 (nat_lit 16285876) (nat_lit 4012785417) (nat_lit 0) D2M8K2.u7719 from rfl, totK_node, atot7716, atot7719]
  decide +kernel

theorem arows7728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7728 = true := by
  rw [show D2M8K2.u7728 = KTree.node D2M8K2.u7724 (nat_lit 16296603) (nat_lit 3660288012) (nat_lit 0) D2M8K2.u7727 from rfl, allE_node, arows7724, irow7728, arows7727]
  all_goals rfl

theorem atot7728 : totK PD2M8K2 D2M8K2.u7728 = [0, 0, 471718321235, 2079776266578, 2895970664485, 1334230171232, 180483713759, 4574395652] := by
  rw [show D2M8K2.u7728 = KTree.node D2M8K2.u7724 (nat_lit 16296603) (nat_lit 3660288012) (nat_lit 0) D2M8K2.u7727 from rfl, totK_node, atot7724, atot7727]
  decide +kernel

theorem arows7735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7735 = true := by
  rw [show D2M8K2.u7735 = KTree.node D2M8K2.u7731 (nat_lit 16347028) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u7734 from rfl, allE_node, arows7731, irow7735, arows7734]
  all_goals rfl

theorem atot7735 : totK PD2M8K2 D2M8K2.u7735 = [0, 0, 817619660843, 2912966260925, 2810814684043, 662124324750, 28063716506, 0] := by
  rw [show D2M8K2.u7735 = KTree.node D2M8K2.u7731 (nat_lit 16347028) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u7734 from rfl, totK_node, atot7731, atot7734]
  decide +kernel

theorem arows7745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7745 = true := by
  rw [show D2M8K2.u7745 = KTree.node D2M8K2.u7741 (nat_lit 16354546) (nat_lit 3641934925) (nat_lit 0) D2M8K2.u7744 from rfl, allE_node, arows7741, irow7745, arows7744]
  all_goals rfl

theorem atot7745 : totK PD2M8K2 D2M8K2.u7745 = [0, 0, 710647103964, 2877582973270, 2888290685036, 573133425817, 20500841507, 0] := by
  rw [show D2M8K2.u7745 = KTree.node D2M8K2.u7741 (nat_lit 16354546) (nat_lit 3641934925) (nat_lit 0) D2M8K2.u7744 from rfl, totK_node, atot7741, atot7744]
  decide +kernel

theorem arows7752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7752 = true := by
  rw [show D2M8K2.u7752 = KTree.node D2M8K2.u7748 (nat_lit 16367886) (nat_lit 2250534116) (nat_lit 0) D2M8K2.u7751 from rfl, allE_node, arows7748, irow7752, arows7751]
  all_goals rfl

theorem atot7752 : totK PD2M8K2 D2M8K2.u7752 = [0, 0, 0, 1492429360532, 3631656085787, 1713177378904, 132071689660, 1103454931] := by
  rw [show D2M8K2.u7752 = KTree.node D2M8K2.u7748 (nat_lit 16367886) (nat_lit 2250534116) (nat_lit 0) D2M8K2.u7751 from rfl, totK_node, atot7748, atot7751]
  decide +kernel

theorem arows7760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7760 = true := by
  rw [show D2M8K2.u7760 = KTree.node D2M8K2.u7756 (nat_lit 16382604) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u7759 from rfl, allE_node, arows7756, irow7760, arows7759]
  all_goals rfl

theorem atot7760 : totK PD2M8K2 D2M8K2.u7760 = [0, 0, 779447178638, 2507047929316, 2531957477615, 1053126800403, 164078487421, 4779662215] := by
  rw [show D2M8K2.u7760 = KTree.node D2M8K2.u7756 (nat_lit 16382604) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u7759 from rfl, totK_node, atot7756, atot7759]
  decide +kernel

theorem arows7767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7767 = true := by
  rw [show D2M8K2.u7767 = KTree.node D2M8K2.u7763 (nat_lit 16389823) (nat_lit 2076581861) (nat_lit 0) D2M8K2.u7766 from rfl, allE_node, arows7763, irow7767, arows7766]
  all_goals rfl

theorem atot7767 : totK PD2M8K2 D2M8K2.u7767 = [0, 0, 877156802654, 3022930675805, 2768784382485, 606227516071, 23476553760, 0] := by
  rw [show D2M8K2.u7767 = KTree.node D2M8K2.u7763 (nat_lit 16389823) (nat_lit 2076581861) (nat_lit 0) D2M8K2.u7766 from rfl, totK_node, atot7763, atot7766]
  decide +kernel

theorem arows7776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7776 = true := by
  rw [show D2M8K2.u7776 = KTree.node D2M8K2.u7772 (nat_lit 16920660) (nat_lit 3271375076) (nat_lit 0) D2M8K2.u7775 from rfl, allE_node, arows7772, irow7776, arows7775]
  all_goals rfl

theorem atot7776 : totK PD2M8K2 D2M8K2.u7776 = [0, 520105745818, 2040198932042, 2715199131819, 1613092350120, 333772553681, 13949453364, 0] := by
  rw [show D2M8K2.u7776 = KTree.node D2M8K2.u7772 (nat_lit 16920660) (nat_lit 3271375076) (nat_lit 0) D2M8K2.u7775 from rfl, totK_node, atot7772, atot7775]
  decide +kernel

theorem arows7783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7783 = true := by
  rw [show D2M8K2.u7783 = KTree.node D2M8K2.u7779 (nat_lit 16931081) (nat_lit 1536060492) (nat_lit 0) D2M8K2.u7782 from rfl, allE_node, arows7779, irow7783, arows7782]
  all_goals rfl

theorem atot7783 : totK PD2M8K2 D2M8K2.u7783 = [0, 812945806327, 2890575018410, 2788628020380, 629284861200, 26300412495, 0, 0] := by
  rw [show D2M8K2.u7783 = KTree.node D2M8K2.u7779 (nat_lit 16931081) (nat_lit 1536060492) (nat_lit 0) D2M8K2.u7782 from rfl, totK_node, atot7779, atot7782]
  decide +kernel

theorem arows7791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7791 = true := by
  rw [show D2M8K2.u7791 = KTree.node D2M8K2.u7787 (nat_lit 16938491) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u7790 from rfl, allE_node, arows7787, irow7791, arows7790]
  all_goals rfl

theorem atot7791 : totK PD2M8K2 D2M8K2.u7791 = [0, 640803445266, 2667197658701, 3020526712614, 787538840024, 29726989231, 0, 0] := by
  rw [show D2M8K2.u7791 = KTree.node D2M8K2.u7787 (nat_lit 16938491) (nat_lit 2879332006) (nat_lit 0) D2M8K2.u7790 from rfl, totK_node, atot7787, atot7790]
  decide +kernel

theorem arows7798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7798 = true := by
  rw [show D2M8K2.u7798 = KTree.node D2M8K2.u7794 (nat_lit 16949552) (nat_lit 3772168480) (nat_lit 0) D2M8K2.u7797 from rfl, allE_node, arows7794, irow7798, arows7797]
  all_goals rfl

theorem atot7798 : totK PD2M8K2 D2M8K2.u7798 = [0, 0, 1258090250192, 3575671075732, 2012303365040, 186780290152, 1369150432, 0] := by
  rw [show D2M8K2.u7798 = KTree.node D2M8K2.u7794 (nat_lit 16949552) (nat_lit 3772168480) (nat_lit 0) D2M8K2.u7797 from rfl, totK_node, atot7794, atot7797]
  decide +kernel

theorem arows7809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7809 = true := by
  rw [show D2M8K2.u7809 = KTree.node D2M8K2.u7805 (nat_lit 16966633) (nat_lit 788521960) (nat_lit 0) D2M8K2.u7808 from rfl, allE_node, arows7805, irow7809, arows7808]
  all_goals rfl

theorem atot7809 : totK PD2M8K2 D2M8K2.u7809 = [0, 600011200564, 2360387465674, 3069026668789, 1168430267527, 65476882297, 0, 0] := by
  rw [show D2M8K2.u7809 = KTree.node D2M8K2.u7805 (nat_lit 16966633) (nat_lit 788521960) (nat_lit 0) D2M8K2.u7808 from rfl, totK_node, atot7805, atot7808]
  decide +kernel

theorem arows7816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7816 = true := by
  rw [show D2M8K2.u7816 = KTree.node D2M8K2.u7812 (nat_lit 16972890) (nat_lit 3681110934) (nat_lit 0) D2M8K2.u7815 from rfl, allE_node, arows7812, irow7816, arows7815]
  all_goals rfl

theorem atot7816 : totK PD2M8K2 D2M8K2.u7816 = [0, 802613445383, 2927077684770, 2863463589073, 629136124729, 25077139050, 0, 0] := by
  rw [show D2M8K2.u7816 = KTree.node D2M8K2.u7812 (nat_lit 16972890) (nat_lit 3681110934) (nat_lit 0) D2M8K2.u7815 from rfl, totK_node, atot7812, atot7815]
  decide +kernel

theorem arows7824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7824 = true := by
  rw [show D2M8K2.u7824 = KTree.node D2M8K2.u7820 (nat_lit 16980169) (nat_lit 1370550316) (nat_lit 0) D2M8K2.u7823 from rfl, allE_node, arows7820, irow7824, arows7823]
  all_goals rfl

theorem atot7824 : totK PD2M8K2 D2M8K2.u7824 = [0, 595440974875, 2568838509649, 3103992493224, 966316680130, 55877522318, 0, 0] := by
  rw [show D2M8K2.u7824 = KTree.node D2M8K2.u7820 (nat_lit 16980169) (nat_lit 1370550316) (nat_lit 0) D2M8K2.u7823 from rfl, totK_node, atot7820, atot7823]
  decide +kernel

theorem arows7831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7831 = true := by
  rw [show D2M8K2.u7831 = KTree.node D2M8K2.u7827 (nat_lit 16990520) (nat_lit 3873616296) (nat_lit 0) D2M8K2.u7830 from rfl, allE_node, arows7827, irow7831, arows7830]
  all_goals rfl

theorem atot7831 : totK PD2M8K2 D2M8K2.u7831 = [0, 0, 867124912677, 3010611361276, 2761025587885, 601761341940, 20248977901, 0] := by
  rw [show D2M8K2.u7831 = KTree.node D2M8K2.u7827 (nat_lit 16990520) (nat_lit 3873616296) (nat_lit 0) D2M8K2.u7830 from rfl, totK_node, atot7827, atot7830]
  decide +kernel

theorem arows7840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7840 = true := by
  rw [show D2M8K2.u7840 = KTree.node D2M8K2.u7836 (nat_lit 16999529) (nat_lit 1657782881) (nat_lit 0) D2M8K2.u7839 from rfl, allE_node, arows7836, irow7840, arows7839]
  all_goals rfl

theorem atot7840 : totK PD2M8K2 D2M8K2.u7840 = [0, 346255259307, 1687249795791, 3022575172189, 1950070821709, 229768202696, 1415142070, 0] := by
  rw [show D2M8K2.u7840 = KTree.node D2M8K2.u7836 (nat_lit 16999529) (nat_lit 1657782881) (nat_lit 0) D2M8K2.u7839 from rfl, totK_node, atot7836, atot7839]
  decide +kernel

theorem arows7847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7847 = true := by
  rw [show D2M8K2.u7847 = KTree.node D2M8K2.u7843 (nat_lit 17008593) (nat_lit 1322783606) (nat_lit 0) D2M8K2.u7846 from rfl, allE_node, arows7843, irow7847, arows7846]
  all_goals rfl

theorem atot7847 : totK PD2M8K2 D2M8K2.u7847 = [0, 784082206840, 2822577170700, 2871094384905, 772300641899, 37268953177, 0, 0] := by
  rw [show D2M8K2.u7847 = KTree.node D2M8K2.u7843 (nat_lit 17008593) (nat_lit 1322783606) (nat_lit 0) D2M8K2.u7846 from rfl, totK_node, atot7843, atot7846]
  decide +kernel

theorem arows7855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7855 = true := by
  rw [show D2M8K2.u7855 = KTree.node D2M8K2.u7851 (nat_lit 17018094) (nat_lit 3122358951) (nat_lit 0) D2M8K2.u7854 from rfl, allE_node, arows7851, irow7855, arows7854]
  all_goals rfl

theorem atot7855 : totK PD2M8K2 D2M8K2.u7855 = [0, 816880132976, 2968407475679, 2852677135319, 578601942389, 18030242193, 0, 0] := by
  rw [show D2M8K2.u7855 = KTree.node D2M8K2.u7851 (nat_lit 17018094) (nat_lit 3122358951) (nat_lit 0) D2M8K2.u7854 from rfl, totK_node, atot7851, atot7854]
  decide +kernel

theorem arows7862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7862 = true := by
  rw [show D2M8K2.u7862 = KTree.node D2M8K2.u7858 (nat_lit 17025779) (nat_lit 2517948873) (nat_lit 128) D2M8K2.u7861 from rfl, allE_node, arows7858, irow7862, arows7861]
  all_goals rfl

theorem atot7862 : totK PD2M8K2 D2M8K2.u7862 = [0, 89240473698, 1474443275917, 3489069641222, 1909520156177, 175990539225, 1206465782, 0] := by
  rw [show D2M8K2.u7862 = KTree.node D2M8K2.u7858 (nat_lit 17025779) (nat_lit 2517948873) (nat_lit 128) D2M8K2.u7861 from rfl, totK_node, atot7858, atot7861]
  decide +kernel

theorem arows7872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7872 = true := by
  rw [show D2M8K2.u7872 = KTree.node D2M8K2.u7868 (nat_lit 17038085) (nat_lit 2314934277) (nat_lit 0) D2M8K2.u7871 from rfl, allE_node, arows7868, irow7872, arows7871]
  all_goals rfl

theorem atot7872 : totK PD2M8K2 D2M8K2.u7872 = [0, 0, 873733967457, 3071865495145, 2606446851125, 485396961349, 17590593026, 0] := by
  rw [show D2M8K2.u7872 = KTree.node D2M8K2.u7868 (nat_lit 17038085) (nat_lit 2314934277) (nat_lit 0) D2M8K2.u7871 from rfl, totK_node, atot7868, atot7871]
  decide +kernel

theorem arows7879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7879 = true := by
  rw [show D2M8K2.u7879 = KTree.node D2M8K2.u7875 (nat_lit 17046871) (nat_lit 2175775974) (nat_lit 0) D2M8K2.u7878 from rfl, allE_node, arows7875, irow7879, arows7878]
  all_goals rfl

theorem atot7879 : totK PD2M8K2 D2M8K2.u7879 = [0, 802680951956, 2856064258798, 2815324233105, 747208554800, 41573529666, 0, 0] := by
  rw [show D2M8K2.u7879 = KTree.node D2M8K2.u7875 (nat_lit 17046871) (nat_lit 2175775974) (nat_lit 0) D2M8K2.u7878 from rfl, totK_node, atot7875, atot7878]
  decide +kernel

theorem arows7887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7887 = true := by
  rw [show D2M8K2.u7887 = KTree.node D2M8K2.u7883 (nat_lit 17057434) (nat_lit 3221757903) (nat_lit 0) D2M8K2.u7886 from rfl, allE_node, arows7883, irow7887, arows7886]
  all_goals rfl

theorem atot7887 : totK PD2M8K2 D2M8K2.u7887 = [0, 849262933305, 2935949419427, 2771667564544, 632787822825, 19777855456, 0, 0] := by
  rw [show D2M8K2.u7887 = KTree.node D2M8K2.u7883 (nat_lit 17057434) (nat_lit 3221757903) (nat_lit 0) D2M8K2.u7886 from rfl, totK_node, atot7883, atot7886]
  decide +kernel

theorem arows7894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7894 = true := by
  rw [show D2M8K2.u7894 = KTree.node D2M8K2.u7890 (nat_lit 17068399) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u7893 from rfl, allE_node, arows7890, irow7894, arows7893]
  all_goals rfl

theorem atot7894 : totK PD2M8K2 D2M8K2.u7894 = [0, 0, 1399119891991, 3688071226702, 1915673884203, 148654287983, 1239866073, 0] := by
  rw [show D2M8K2.u7894 = KTree.node D2M8K2.u7890 (nat_lit 17068399) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u7893 from rfl, totK_node, atot7890, atot7893]
  decide +kernel

theorem arows7903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7903 = true := by
  rw [show D2M8K2.u7903 = KTree.node D2M8K2.u7899 (nat_lit 17081964) (nat_lit 2856613793) (nat_lit 0) D2M8K2.u7902 from rfl, allE_node, arows7899, irow7903, arows7902]
  all_goals rfl

theorem atot7903 : totK PD2M8K2 D2M8K2.u7903 = [0, 412428170261, 1911295229608, 2969198078554, 1555712994984, 196752090161, 4720618446, 0] := by
  rw [show D2M8K2.u7903 = KTree.node D2M8K2.u7899 (nat_lit 17081964) (nat_lit 2856613793) (nat_lit 0) D2M8K2.u7902 from rfl, totK_node, atot7899, atot7902]
  decide +kernel

theorem arows7910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7910 = true := by
  rw [show D2M8K2.u7910 = KTree.node D2M8K2.u7906 (nat_lit 17092629) (nat_lit 1730766126) (nat_lit 0) D2M8K2.u7909 from rfl, allE_node, arows7906, irow7910, arows7909]
  all_goals rfl

theorem atot7910 : totK PD2M8K2 D2M8K2.u7910 = [0, 844456967963, 2864053259712, 2751986082236, 746207203207, 37134689990, 0, 0] := by
  rw [show D2M8K2.u7910 = KTree.node D2M8K2.u7906 (nat_lit 17092629) (nat_lit 1730766126) (nat_lit 0) D2M8K2.u7909 from rfl, totK_node, atot7906, atot7909]
  decide +kernel

theorem arows7918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7918 = true := by
  rw [show D2M8K2.u7918 = KTree.node D2M8K2.u7914 (nat_lit 17098940) (nat_lit 3290411903) (nat_lit 0) D2M8K2.u7917 from rfl, allE_node, arows7914, irow7918, arows7917]
  all_goals rfl

theorem atot7918 : totK PD2M8K2 D2M8K2.u7918 = [0, 845448351338, 2907579592822, 2760490389949, 623646461334, 26232597979, 0, 0] := by
  rw [show D2M8K2.u7918 = KTree.node D2M8K2.u7914 (nat_lit 17098940) (nat_lit 3290411903) (nat_lit 0) D2M8K2.u7917 from rfl, totK_node, atot7914, atot7917]
  decide +kernel

theorem arows7925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7925 = true := by
  rw [show D2M8K2.u7925 = KTree.node D2M8K2.u7921 (nat_lit 17109574) (nat_lit 2472076944) (nat_lit 0) D2M8K2.u7924 from rfl, allE_node, arows7921, irow7925, arows7924]
  all_goals rfl

theorem atot7925 : totK PD2M8K2 D2M8K2.u7925 = [0, 0, 1394507434424, 3656031517873, 1898880739542, 166420967755, 1138244013, 0] := by
  rw [show D2M8K2.u7925 = KTree.node D2M8K2.u7921 (nat_lit 17109574) (nat_lit 2472076944) (nat_lit 0) D2M8K2.u7924 from rfl, totK_node, atot7921, atot7924]
  decide +kernel

theorem arows7937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7937 = true := by
  rw [show D2M8K2.u7937 = KTree.node D2M8K2.u7933 (nat_lit 17121416) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u7936 from rfl, allE_node, arows7933, irow7937, arows7936]
  all_goals rfl

theorem atot7937 : totK PD2M8K2 D2M8K2.u7937 = [0, 0, 1220479260814, 3483564509793, 2139899615732, 266921884940, 4977114383, 0] := by
  rw [show D2M8K2.u7937 = KTree.node D2M8K2.u7933 (nat_lit 17121416) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u7936 from rfl, totK_node, atot7933, atot7936]
  decide +kernel

theorem arows7944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7944 = true := by
  rw [show D2M8K2.u7944 = KTree.node D2M8K2.u7940 (nat_lit 17176918) (nat_lit 3489286276) (nat_lit 0) D2M8K2.u7943 from rfl, allE_node, arows7940, irow7944, arows7943]
  all_goals rfl

theorem atot7944 : totK PD2M8K2 D2M8K2.u7944 = [0, 0, 890435641495, 3059745300626, 2678438402045, 453042700614, 14352600228, 0] := by
  rw [show D2M8K2.u7944 = KTree.node D2M8K2.u7940 (nat_lit 17176918) (nat_lit 3489286276) (nat_lit 0) D2M8K2.u7943 from rfl, totK_node, atot7940, atot7943]
  decide +kernel

theorem arows7952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7952 = true := by
  rw [show D2M8K2.u7952 = KTree.node D2M8K2.u7948 (nat_lit 17184404) (nat_lit 3298673335) (nat_lit 0) D2M8K2.u7951 from rfl, allE_node, arows7948, irow7952, arows7951]
  all_goals rfl

theorem atot7952 : totK PD2M8K2 D2M8K2.u7952 = [0, 0, 892524332014, 3227304987884, 2592256759430, 351314680913, 7447327654, 0] := by
  rw [show D2M8K2.u7952 = KTree.node D2M8K2.u7948 (nat_lit 17184404) (nat_lit 3298673335) (nat_lit 0) D2M8K2.u7951 from rfl, totK_node, atot7948, atot7951]
  decide +kernel

theorem arows7959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7959 = true := by
  rw [show D2M8K2.u7959 = KTree.node D2M8K2.u7955 (nat_lit 17197061) (nat_lit 2330038851) (nat_lit 0) D2M8K2.u7958 from rfl, allE_node, arows7955, irow7959, arows7958]
  all_goals rfl

theorem atot7959 : totK PD2M8K2 D2M8K2.u7959 = [0, 0, 0, 1617836659186, 3746357738018, 1481779780213, 103492673793, 1209030869] := by
  rw [show D2M8K2.u7959 = KTree.node D2M8K2.u7955 (nat_lit 17197061) (nat_lit 2330038851) (nat_lit 0) D2M8K2.u7958 from rfl, totK_node, atot7955, atot7958]
  decide +kernel

theorem arows7968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7968 = true := by
  rw [show D2M8K2.u7968 = KTree.node D2M8K2.u7964 (nat_lit 17215569) (nat_lit 1856181051) (nat_lit 0) D2M8K2.u7967 from rfl, allE_node, arows7964, irow7968, arows7967]
  all_goals rfl

theorem atot7968 : totK PD2M8K2 D2M8K2.u7968 = [0, 0, 741781019287, 2802189225128, 2983450032787, 729447494837, 29981017833, 0] := by
  rw [show D2M8K2.u7968 = KTree.node D2M8K2.u7964 (nat_lit 17215569) (nat_lit 1856181051) (nat_lit 0) D2M8K2.u7967 from rfl, totK_node, atot7964, atot7967]
  decide +kernel

theorem arows7975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7975 = true := by
  rw [show D2M8K2.u7975 = KTree.node D2M8K2.u7971 (nat_lit 17222782) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u7974 from rfl, allE_node, arows7971, irow7975, arows7974]
  all_goals rfl

theorem atot7975 : totK PD2M8K2 D2M8K2.u7975 = [0, 0, 1004451320814, 3210491441757, 2619804066419, 426773141793, 12565280906, 0] := by
  rw [show D2M8K2.u7975 = KTree.node D2M8K2.u7971 (nat_lit 17222782) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u7974 from rfl, totK_node, atot7971, atot7974]
  decide +kernel

theorem arows7983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7983 = true := by
  rw [show D2M8K2.u7983 = KTree.node D2M8K2.u7979 (nat_lit 17254678) (nat_lit 3323736924) (nat_lit 0) D2M8K2.u7982 from rfl, allE_node, arows7979, irow7983, arows7982]
  all_goals rfl

theorem atot7983 : totK PD2M8K2 D2M8K2.u7983 = [0, 0, 1060778484458, 3264344272710, 2492837330213, 413030000696, 14914595397, 0] := by
  rw [show D2M8K2.u7983 = KTree.node D2M8K2.u7979 (nat_lit 17254678) (nat_lit 3323736924) (nat_lit 0) D2M8K2.u7982 from rfl, totK_node, atot7979, atot7982]
  decide +kernel

theorem arows7990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7990 = true := by
  rw [show D2M8K2.u7990 = KTree.node D2M8K2.u7986 (nat_lit 17261620) (nat_lit 4076853445) (nat_lit 0) D2M8K2.u7989 from rfl, allE_node, arows7986, irow7990, arows7989]
  all_goals rfl

theorem atot7990 : totK PD2M8K2 D2M8K2.u7990 = [0, 0, 858093865176, 3018606259712, 2767520278962, 531703007593, 15555793151, 0] := by
  rw [show D2M8K2.u7990 = KTree.node D2M8K2.u7986 (nat_lit 17261620) (nat_lit 4076853445) (nat_lit 0) D2M8K2.u7989 from rfl, totK_node, atot7986, atot7989]
  decide +kernel

theorem arows8000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8000 = true := by
  rw [show D2M8K2.u8000 = KTree.node D2M8K2.u7996 (nat_lit 17272864) (nat_lit 3736483650) (nat_lit 0) D2M8K2.u7999 from rfl, allE_node, arows7996, irow8000, arows7999]
  all_goals rfl

theorem atot8000 : totK PD2M8K2 D2M8K2.u8000 = [0, 0, 866447333546, 3130665938240, 2743002391941, 432410468534, 10075422199, 0] := by
  rw [show D2M8K2.u8000 = KTree.node D2M8K2.u7996 (nat_lit 17272864) (nat_lit 3736483650) (nat_lit 0) D2M8K2.u7999 from rfl, totK_node, atot7996, atot7999]
  decide +kernel

theorem arows8007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8007 = true := by
  rw [show D2M8K2.u8007 = KTree.node D2M8K2.u8003 (nat_lit 17308017) (nat_lit 1835327690) (nat_lit 0) D2M8K2.u8006 from rfl, allE_node, arows8003, irow8007, arows8006]
  all_goals rfl

theorem atot8007 : totK PD2M8K2 D2M8K2.u8007 = [0, 0, 1293389122320, 3538642366639, 2131082373995, 242816293919, 4980514959, 0] := by
  rw [show D2M8K2.u8007 = KTree.node D2M8K2.u8003 (nat_lit 17308017) (nat_lit 1835327690) (nat_lit 0) D2M8K2.u8006 from rfl, totK_node, atot8003, atot8006]
  decide +kernel

theorem arows8015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8015 = true := by
  rw [show D2M8K2.u8015 = KTree.node D2M8K2.u8011 (nat_lit 17339726) (nat_lit 3818987115) (nat_lit 0) D2M8K2.u8014 from rfl, allE_node, arows8011, irow8015, arows8014]
  all_goals rfl

theorem atot8015 : totK PD2M8K2 D2M8K2.u8015 = [0, 0, 909706945792, 3053771502076, 2654528739564, 490563604350, 16362040986, 0] := by
  rw [show D2M8K2.u8015 = KTree.node D2M8K2.u8011 (nat_lit 17339726) (nat_lit 3818987115) (nat_lit 0) D2M8K2.u8014 from rfl, totK_node, atot8011, atot8014]
  decide +kernel

theorem arows8022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8022 = true := by
  rw [show D2M8K2.u8022 = KTree.node D2M8K2.u8018 (nat_lit 17346680) (nat_lit 3489231784) (nat_lit 0) D2M8K2.u8021 from rfl, allE_node, arows8018, irow8022, arows8021]
  all_goals rfl

theorem atot8022 : totK PD2M8K2 D2M8K2.u8022 = [0, 0, 899154982995, 3050120153961, 2656982495966, 488431542013, 17653956135, 0] := by
  rw [show D2M8K2.u8022 = KTree.node D2M8K2.u8018 (nat_lit 17346680) (nat_lit 3489231784) (nat_lit 0) D2M8K2.u8021 from rfl, totK_node, atot8018, atot8021]
  decide +kernel

theorem arows8031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8031 = true := by
  rw [show D2M8K2.u8031 = KTree.node D2M8K2.u8027 (nat_lit 17357426) (nat_lit 3784960859) (nat_lit 0) D2M8K2.u8030 from rfl, allE_node, arows8027, irow8031, arows8030]
  all_goals rfl

theorem atot8031 : totK PD2M8K2 D2M8K2.u8031 = [0, 0, 92932490688, 1721154550472, 3581619388418, 1478843291889, 115603283642, 1138244013] := by
  rw [show D2M8K2.u8031 = KTree.node D2M8K2.u8027 (nat_lit 17357426) (nat_lit 3784960859) (nat_lit 0) D2M8K2.u8030 from rfl, totK_node, atot8027, atot8030]
  decide +kernel

theorem arows8038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8038 = true := by
  rw [show D2M8K2.u8038 = KTree.node D2M8K2.u8034 (nat_lit 17370701) (nat_lit 1845771498) (nat_lit 0) D2M8K2.u8037 from rfl, allE_node, arows8034, irow8038, arows8037]
  all_goals rfl

theorem atot8038 : totK PD2M8K2 D2M8K2.u8038 = [0, 344808557977, 782004390955, 1398037433171, 2767872878712, 1543177704389, 196507295341, 4977114383] := by
  rw [show D2M8K2.u8038 = KTree.node D2M8K2.u8034 (nat_lit 17370701) (nat_lit 1845771498) (nat_lit 0) D2M8K2.u8037 from rfl, totK_node, atot8034, atot8037]
  decide +kernel

theorem arows8046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8046 = true := by
  rw [show D2M8K2.u8046 = KTree.node D2M8K2.u8042 (nat_lit 17426612) (nat_lit 2585600523) (nat_lit 0) D2M8K2.u8045 from rfl, allE_node, arows8042, irow8046, arows8045]
  all_goals rfl

theorem atot8046 : totK PD2M8K2 D2M8K2.u8046 = [0, 835335340188, 3023779422545, 2787662294493, 526072901438, 14418877666, 0, 0] := by
  rw [show D2M8K2.u8046 = KTree.node D2M8K2.u8042 (nat_lit 17426612) (nat_lit 2585600523) (nat_lit 0) D2M8K2.u8045 from rfl, totK_node, atot8042, atot8045]
  decide +kernel

theorem arows8053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8053 = true := by
  rw [show D2M8K2.u8053 = KTree.node D2M8K2.u8049 (nat_lit 17434372) (nat_lit 3818132245) (nat_lit 0) D2M8K2.u8052 from rfl, allE_node, arows8049, irow8053, arows8052]
  all_goals rfl

theorem atot8053 : totK PD2M8K2 D2M8K2.u8053 = [0, 795093944613, 2970187332293, 2840517374121, 550632525442, 11704901802, 0, 0] := by
  rw [show D2M8K2.u8053 = KTree.node D2M8K2.u8049 (nat_lit 17434372) (nat_lit 3818132245) (nat_lit 0) D2M8K2.u8052 from rfl, totK_node, atot8049, atot8052]
  decide +kernel

theorem arows8064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8064 = true := by
  rw [show D2M8K2.u8064 = KTree.node D2M8K2.u8060 (nat_lit 17440896) (nat_lit 3567842173) (nat_lit 0) D2M8K2.u8063 from rfl, allE_node, arows8060, irow8064, arows8063]
  all_goals rfl

theorem atot8064 : totK PD2M8K2 D2M8K2.u8064 = [0, 0, 1228578045945, 3555933469049, 2066031151176, 199021859018, 1369150432, 0] := by
  rw [show D2M8K2.u8064 = KTree.node D2M8K2.u8060 (nat_lit 17440896) (nat_lit 3567842173) (nat_lit 0) D2M8K2.u8063 from rfl, totK_node, atot8060, atot8063]
  decide +kernel

theorem arows8071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8071 = true := by
  rw [show D2M8K2.u8071 = KTree.node D2M8K2.u8067 (nat_lit 17456942) (nat_lit 2976483464) (nat_lit 0) D2M8K2.u8070 from rfl, allE_node, arows8067, irow8071, arows8070]
  all_goals rfl

theorem atot8071 : totK PD2M8K2 D2M8K2.u8071 = [0, 442886995791, 2200805235432, 3281643540894, 1225748276213, 58696018738, 0, 0] := by
  rw [show D2M8K2.u8071 = KTree.node D2M8K2.u8067 (nat_lit 17456942) (nat_lit 2976483464) (nat_lit 0) D2M8K2.u8070 from rfl, totK_node, atot8067, atot8070]
  decide +kernel

theorem arows8079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8079 = true := by
  rw [show D2M8K2.u8079 = KTree.node D2M8K2.u8075 (nat_lit 17468113) (nat_lit 1456748985) (nat_lit 0) D2M8K2.u8078 from rfl, allE_node, arows8075, irow8079, arows8078]
  all_goals rfl

theorem atot8079 : totK PD2M8K2 D2M8K2.u8079 = [0, 787101737093, 2708812010616, 2851106652398, 879335381092, 49642193482, 0, 0] := by
  rw [show D2M8K2.u8079 = KTree.node D2M8K2.u8075 (nat_lit 17468113) (nat_lit 1456748985) (nat_lit 0) D2M8K2.u8078 from rfl, totK_node, atot8075, atot8078]
  decide +kernel

theorem arows8086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8086 = true := by
  rw [show D2M8K2.u8086 = KTree.node D2M8K2.u8082 (nat_lit 17475860) (nat_lit 3147407277) (nat_lit 0) D2M8K2.u8085 from rfl, allE_node, arows8082, irow8086, arows8085]
  all_goals rfl

theorem atot8086 : totK PD2M8K2 D2M8K2.u8086 = [0, 773509972798, 2985031143294, 2960006848696, 591537702116, 13671043621, 0, 0] := by
  rw [show D2M8K2.u8086 = KTree.node D2M8K2.u8082 (nat_lit 17475860) (nat_lit 3147407277) (nat_lit 0) D2M8K2.u8085 from rfl, totK_node, atot8082, atot8085]
  decide +kernel

theorem arows8095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8095 = true := by
  rw [show D2M8K2.u8095 = KTree.node D2M8K2.u8091 (nat_lit 17486056) (nat_lit 3742480606) (nat_lit 0) D2M8K2.u8094 from rfl, allE_node, arows8091, irow8095, arows8094]
  all_goals rfl

theorem atot8095 : totK PD2M8K2 D2M8K2.u8095 = [0, 0, 1052681341133, 3097181049624, 2446368047722, 603333386225, 33015336044, 0] := by
  rw [show D2M8K2.u8095 = KTree.node D2M8K2.u8091 (nat_lit 17486056) (nat_lit 3742480606) (nat_lit 0) D2M8K2.u8094 from rfl, totK_node, atot8091, atot8094]
  decide +kernel

theorem arows8102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8102 = true := by
  rw [show D2M8K2.u8102 = KTree.node D2M8K2.u8098 (nat_lit 17492557) (nat_lit 1326993281) (nat_lit 0) D2M8K2.u8101 from rfl, allE_node, arows8098, irow8102, arows8101]
  all_goals rfl

theorem atot8102 : totK PD2M8K2 D2M8K2.u8102 = [0, 0, 733398737617, 3069212226072, 3002967385405, 504012193929, 6717450418, 0] := by
  rw [show D2M8K2.u8102 = KTree.node D2M8K2.u8098 (nat_lit 17492557) (nat_lit 1326993281) (nat_lit 0) D2M8K2.u8101 from rfl, totK_node, atot8098, atot8101]
  decide +kernel

theorem arows8110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8110 = true := by
  rw [show D2M8K2.u8110 = KTree.node D2M8K2.u8106 (nat_lit 17501118) (nat_lit 3958671284) (nat_lit 0) D2M8K2.u8109 from rfl, allE_node, arows8106, irow8110, arows8109]
  all_goals rfl

theorem atot8110 : totK PD2M8K2 D2M8K2.u8110 = [0, 500980042477, 2008890848765, 2757183446745, 1590821496903, 326819105615, 10717512769, 0] := by
  rw [show D2M8K2.u8110 = KTree.node D2M8K2.u8106 (nat_lit 17501118) (nat_lit 3958671284) (nat_lit 0) D2M8K2.u8109 from rfl, totK_node, atot8106, atot8109]
  decide +kernel

theorem arows8117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8117 = true := by
  rw [show D2M8K2.u8117 = KTree.node D2M8K2.u8113 (nat_lit 17507869) (nat_lit 1130557898) (nat_lit 0) D2M8K2.u8116 from rfl, allE_node, arows8113, irow8117, arows8116]
  all_goals rfl

theorem atot8117 : totK PD2M8K2 D2M8K2.u8117 = [0, 767653286534, 2780125601257, 2859386992337, 839125132908, 45601524537, 0, 0] := by
  rw [show D2M8K2.u8117 = KTree.node D2M8K2.u8113 (nat_lit 17507869) (nat_lit 1130557898) (nat_lit 0) D2M8K2.u8116 from rfl, totK_node, atot8113, atot8116]
  decide +kernel

theorem arows8127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8127 = true := by
  rw [show D2M8K2.u8127 = KTree.node D2M8K2.u8123 (nat_lit 17518581) (nat_lit 1618021349) (nat_lit 0) D2M8K2.u8126 from rfl, allE_node, arows8123, irow8127, arows8126]
  all_goals rfl

theorem atot8127 : totK PD2M8K2 D2M8K2.u8127 = [0, 771091638455, 2878916548992, 2922581033467, 643909995982, 17150729827, 0, 0] := by
  rw [show D2M8K2.u8127 = KTree.node D2M8K2.u8123 (nat_lit 17518581) (nat_lit 1618021349) (nat_lit 0) D2M8K2.u8126 from rfl, totK_node, atot8123, atot8126]
  decide +kernel

theorem arows8134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8134 = true := by
  rw [show D2M8K2.u8134 = KTree.node D2M8K2.u8130 (nat_lit 17525867) (nat_lit 2726664454) (nat_lit 0) D2M8K2.u8133 from rfl, allE_node, arows8130, irow8134, arows8133]
  all_goals rfl

theorem atot8134 : totK PD2M8K2 D2M8K2.u8134 = [0, 0, 1242154974415, 3564855942752, 2147355511884, 204421128982, 1206465782, 0] := by
  rw [show D2M8K2.u8134 = KTree.node D2M8K2.u8130 (nat_lit 17525867) (nat_lit 2726664454) (nat_lit 0) D2M8K2.u8133 from rfl, totK_node, atot8130, atot8133]
  decide +kernel

theorem arows8142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8142 = true := by
  rw [show D2M8K2.u8142 = KTree.node D2M8K2.u8138 (nat_lit 17539272) (nat_lit 3575372299) (nat_lit 0) D2M8K2.u8141 from rfl, allE_node, arows8138, irow8142, arows8141]
  all_goals rfl

theorem atot8142 : totK PD2M8K2 D2M8K2.u8142 = [0, 342231832570, 1623653580409, 2886279630951, 1932413452326, 345283724911, 13016197374, 0] := by
  rw [show D2M8K2.u8142 = KTree.node D2M8K2.u8138 (nat_lit 17539272) (nat_lit 3575372299) (nat_lit 0) D2M8K2.u8141 from rfl, totK_node, atot8138, atot8141]
  decide +kernel

theorem arows8149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8149 = true := by
  rw [show D2M8K2.u8149 = KTree.node D2M8K2.u8145 (nat_lit 17547822) (nat_lit 3828050295) (nat_lit 0) D2M8K2.u8148 from rfl, allE_node, arows8145, irow8149, arows8148]
  all_goals rfl

theorem atot8149 : totK PD2M8K2 D2M8K2.u8149 = [0, 796009015270, 2851406748340, 2854988650297, 740101250856, 35025299072, 0, 0] := by
  rw [show D2M8K2.u8149 = KTree.node D2M8K2.u8145 (nat_lit 17547822) (nat_lit 3828050295) (nat_lit 0) D2M8K2.u8148 from rfl, totK_node, atot8145, atot8148]
  decide +kernel

theorem arows8158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8158 = true := by
  rw [show D2M8K2.u8158 = KTree.node D2M8K2.u8154 (nat_lit 17560922) (nat_lit 4038554353) (nat_lit 0) D2M8K2.u8157 from rfl, allE_node, arows8154, irow8158, arows8157]
  all_goals rfl

theorem atot8158 : totK PD2M8K2 D2M8K2.u8158 = [0, 516265476472, 2451206771609, 3224917172438, 962288514596, 38997944939, 0, 0] := by
  rw [show D2M8K2.u8158 = KTree.node D2M8K2.u8154 (nat_lit 17560922) (nat_lit 4038554353) (nat_lit 0) D2M8K2.u8157 from rfl, totK_node, atot8154, atot8157]
  decide +kernel

theorem arows8165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8165 = true := by
  rw [show D2M8K2.u8165 = KTree.node D2M8K2.u8161 (nat_lit 17568336) (nat_lit 2662715229) (nat_lit 0) D2M8K2.u8164 from rfl, allE_node, arows8161, irow8165, arows8164]
  all_goals rfl

theorem atot8165 : totK PD2M8K2 D2M8K2.u8165 = [0, 0, 985640738467, 3285316132556, 2552624368193, 336784725799, 6665697270, 0] := by
  rw [show D2M8K2.u8165 = KTree.node D2M8K2.u8161 (nat_lit 17568336) (nat_lit 2662715229) (nat_lit 0) D2M8K2.u8164 from rfl, totK_node, atot8161, atot8164]
  decide +kernel

theorem arows8173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8173 = true := by
  rw [show D2M8K2.u8173 = KTree.node D2M8K2.u8169 (nat_lit 17626800) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u8172 from rfl, allE_node, arows8169, irow8173, arows8172]
  all_goals rfl

theorem atot8173 : totK PD2M8K2 D2M8K2.u8173 = [0, 748105177648, 2704616088715, 2829960643362, 880421557662, 58838114446, 0, 0] := by
  rw [show D2M8K2.u8173 = KTree.node D2M8K2.u8169 (nat_lit 17626800) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u8172 from rfl, totK_node, atot8169, atot8172]
  decide +kernel

theorem arows8180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8180 = true := by
  rw [show D2M8K2.u8180 = KTree.node D2M8K2.u8176 (nat_lit 17633138) (nat_lit 4082330911) (nat_lit 0) D2M8K2.u8179 from rfl, allE_node, arows8176, irow8180, arows8179]
  all_goals rfl

theorem atot8180 : totK PD2M8K2 D2M8K2.u8180 = [0, 683913066476, 2646175574082, 2963896705509, 896120687147, 46480772512, 0, 0] := by
  rw [show D2M8K2.u8180 = KTree.node D2M8K2.u8176 (nat_lit 17633138) (nat_lit 4082330911) (nat_lit 0) D2M8K2.u8179 from rfl, totK_node, atot8176, atot8179]
  decide +kernel

theorem arows8197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8197 = true := by
  rw [show D2M8K2.u8197 = KTree.node D2M8K2.u8193 (nat_lit 17643466) (nat_lit 3918663076) (nat_lit 0) D2M8K2.u8196 from rfl, allE_node, arows8193, irow8197, arows8196]
  all_goals rfl

theorem atot8197 : totK PD2M8K2 D2M8K2.u8197 = [0, 679887205274, 2680574794781, 3019659354978, 811226478330, 32332031899, 0, 0] := by
  rw [show D2M8K2.u8197 = KTree.node D2M8K2.u8193 (nat_lit 17643466) (nat_lit 3918663076) (nat_lit 0) D2M8K2.u8196 from rfl, totK_node, atot8193, atot8196]
  decide +kernel

theorem arows8204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8204 = true := by
  rw [show D2M8K2.u8204 = KTree.node D2M8K2.u8200 (nat_lit 17650510) (nat_lit 4004602945) (nat_lit 0) D2M8K2.u8203 from rfl, allE_node, arows8200, irow8204, arows8203]
  all_goals rfl

theorem atot8204 : totK PD2M8K2 D2M8K2.u8204 = [0, 0, 1164619529752, 3460094519852, 2323777385433, 228908150891, 1310285577, 0] := by
  rw [show D2M8K2.u8204 = KTree.node D2M8K2.u8200 (nat_lit 17650510) (nat_lit 4004602945) (nat_lit 0) D2M8K2.u8203 from rfl, totK_node, atot8200, atot8203]
  decide +kernel

theorem arows8212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8212 = true := by
  rw [show D2M8K2.u8212 = KTree.node D2M8K2.u8208 (nat_lit 17658764) (nat_lit 2439712994) (nat_lit 512) D2M8K2.u8211 from rfl, allE_node, arows8208, irow8212, arows8211]
  all_goals rfl

theorem atot8212 : totK PD2M8K2 D2M8K2.u8212 = [0, 0, 846503265602, 3051198859696, 2751226302372, 484712094710, 11053383638, 0] := by
  rw [show D2M8K2.u8212 = KTree.node D2M8K2.u8208 (nat_lit 17658764) (nat_lit 2439712994) (nat_lit 512) D2M8K2.u8211 from rfl, totK_node, atot8208, atot8211]
  decide +kernel

theorem arows8219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8219 = true := by
  rw [show D2M8K2.u8219 = KTree.node D2M8K2.u8215 (nat_lit 17917729) (nat_lit 1511738784) (nat_lit 0) D2M8K2.u8218 from rfl, allE_node, arows8215, irow8219, arows8218]
  all_goals rfl

theorem atot8219 : totK PD2M8K2 D2M8K2.u8219 = [842186864805, 2693244393491, 2086770459372, 564111765307, 668989632431, 291561216614, 20509029466, 0] := by
  rw [show D2M8K2.u8219 = KTree.node D2M8K2.u8215 (nat_lit 17917729) (nat_lit 1511738784) (nat_lit 0) D2M8K2.u8218 from rfl, totK_node, atot8215, atot8218]
  decide +kernel

theorem arows8228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8228 = true := by
  rw [show D2M8K2.u8228 = KTree.node D2M8K2.u8224 (nat_lit 17928247) (nat_lit 2214148709) (nat_lit 0) D2M8K2.u8227 from rfl, allE_node, arows8224, irow8228, arows8227]
  all_goals rfl

theorem atot8228 : totK PD2M8K2 D2M8K2.u8228 = [835588804452, 2924367803712, 2747576512565, 610940684573, 25136092875, 0, 0, 0] := by
  rw [show D2M8K2.u8228 = KTree.node D2M8K2.u8224 (nat_lit 17928247) (nat_lit 2214148709) (nat_lit 0) D2M8K2.u8227 from rfl, totK_node, atot8224, atot8227]
  decide +kernel

theorem arows8235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8235 = true := by
  rw [show D2M8K2.u8235 = KTree.node D2M8K2.u8231 (nat_lit 17935106) (nat_lit 3171398293) (nat_lit 0) D2M8K2.u8234 from rfl, allE_node, arows8231, irow8235, arows8234]
  all_goals rfl

theorem atot8235 : totK PD2M8K2 D2M8K2.u8235 = [419241756986, 2255727194615, 3312953685123, 1090211454608, 50108249389, 0, 0, 0] := by
  rw [show D2M8K2.u8235 = KTree.node D2M8K2.u8231 (nat_lit 17935106) (nat_lit 3171398293) (nat_lit 0) D2M8K2.u8234 from rfl, totK_node, atot8231, atot8234]
  decide +kernel

theorem arows8243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8243 = true := by
  rw [show D2M8K2.u8243 = KTree.node D2M8K2.u8239 (nat_lit 17947162) (nat_lit 3804504321) (nat_lit 0) D2M8K2.u8242 from rfl, allE_node, arows8239, irow8243, arows8242]
  all_goals rfl

theorem atot8243 : totK PD2M8K2 D2M8K2.u8243 = [0, 1232050900628, 3515240336010, 2095497072035, 214201041770, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8243 = KTree.node D2M8K2.u8239 (nat_lit 17947162) (nat_lit 3804504321) (nat_lit 0) D2M8K2.u8242 from rfl, totK_node, atot8239, atot8242]
  decide +kernel

theorem arows8250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8250 = true := by
  rw [show D2M8K2.u8250 = KTree.node D2M8K2.u8246 (nat_lit 18000085) (nat_lit 1248762422) (nat_lit 0) D2M8K2.u8249 from rfl, allE_node, arows8246, irow8250, arows8249]
  all_goals rfl

theorem atot8250 : totK PD2M8K2 D2M8K2.u8250 = [759475109194, 2760508476160, 2829945480481, 808756881540, 34998417337, 0, 0, 0] := by
  rw [show D2M8K2.u8250 = KTree.node D2M8K2.u8246 (nat_lit 18000085) (nat_lit 1248762422) (nat_lit 0) D2M8K2.u8249 from rfl, totK_node, atot8246, atot8249]
  decide +kernel

theorem arows8260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8260 = true := by
  rw [show D2M8K2.u8260 = KTree.node D2M8K2.u8256 (nat_lit 18013713) (nat_lit 1590662519) (nat_lit 0) D2M8K2.u8259 from rfl, allE_node, arows8256, irow8260, arows8259]
  all_goals rfl

theorem atot8260 : totK PD2M8K2 D2M8K2.u8260 = [851456246190, 2946776003110, 2790004241480, 578409935795, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u8260 = KTree.node D2M8K2.u8256 (nat_lit 18013713) (nat_lit 1590662519) (nat_lit 0) D2M8K2.u8259 from rfl, totK_node, atot8256, atot8259]
  decide +kernel

theorem arows8267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8267 = true := by
  rw [show D2M8K2.u8267 = KTree.node D2M8K2.u8263 (nat_lit 18020930) (nat_lit 3579895888) (nat_lit 0) D2M8K2.u8266 from rfl, allE_node, arows8263, irow8267, arows8266]
  all_goals rfl

theorem atot8267 : totK PD2M8K2 D2M8K2.u8267 = [37220374354, 1400149126052, 3543978120161, 1941813718629, 170525689714, 1206465782, 0, 0] := by
  rw [show D2M8K2.u8267 = KTree.node D2M8K2.u8263 (nat_lit 18020930) (nat_lit 3579895888) (nat_lit 0) D2M8K2.u8266 from rfl, totK_node, atot8263, atot8266]
  decide +kernel

theorem arows8275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8275 = true := by
  rw [show D2M8K2.u8275 = KTree.node D2M8K2.u8271 (nat_lit 18034733) (nat_lit 2015909635) (nat_lit 0) D2M8K2.u8274 from rfl, allE_node, arows8271, irow8275, arows8274]
  all_goals rfl

theorem atot8275 : totK PD2M8K2 D2M8K2.u8275 = [72314505312, 898361627942, 2920381216107, 2621222718660, 498699553959, 17590593026, 0, 0] := by
  rw [show D2M8K2.u8275 = KTree.node D2M8K2.u8271 (nat_lit 18034733) (nat_lit 2015909635) (nat_lit 0) D2M8K2.u8274 from rfl, totK_node, atot8271, atot8274]
  decide +kernel

theorem arows8282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8282 = true := by
  rw [show D2M8K2.u8282 = KTree.node D2M8K2.u8278 (nat_lit 18044322) (nat_lit 3299736308) (nat_lit 0) D2M8K2.u8281 from rfl, allE_node, arows8278, irow8282, arows8281]
  all_goals rfl

theorem atot8282 : totK PD2M8K2 D2M8K2.u8282 = [864995468318, 2965620006024, 2752550880225, 675684613154, 34715539287, 0, 0, 0] := by
  rw [show D2M8K2.u8282 = KTree.node D2M8K2.u8278 (nat_lit 18044322) (nat_lit 3299736308) (nat_lit 0) D2M8K2.u8281 from rfl, totK_node, atot8278, atot8281]
  decide +kernel

theorem arows8291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8291 = true := by
  rw [show D2M8K2.u8291 = KTree.node D2M8K2.u8287 (nat_lit 18054369) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u8290 from rfl, allE_node, arows8287, irow8291, arows8290]
  all_goals rfl

theorem atot8291 : totK PD2M8K2 D2M8K2.u8291 = [800858274147, 2943606703842, 2864182172754, 593528591617, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u8291 = KTree.node D2M8K2.u8287 (nat_lit 18054369) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u8290 from rfl, totK_node, atot8287, atot8290]
  decide +kernel

theorem arows8298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8298 = true := by
  rw [show D2M8K2.u8298 = KTree.node D2M8K2.u8294 (nat_lit 18061160) (nat_lit 3848921410) (nat_lit 0) D2M8K2.u8297 from rfl, allE_node, arows8294, irow8298, arows8297]
  all_goals rfl

theorem atot8298 : totK PD2M8K2 D2M8K2.u8298 = [296693726884, 1767461836876, 3213398372165, 1729994406658, 167147836108, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8298 = KTree.node D2M8K2.u8294 (nat_lit 18061160) (nat_lit 3848921410) (nat_lit 0) D2M8K2.u8297 from rfl, totK_node, atot8294, atot8297]
  decide +kernel

theorem arows8306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8306 = true := by
  rw [show D2M8K2.u8306 = KTree.node D2M8K2.u8302 (nat_lit 18073352) (nat_lit 3021629160) (nat_lit 0) D2M8K2.u8305 from rfl, allE_node, arows8302, irow8306, arows8305]
  all_goals rfl

theorem atot8306 : totK PD2M8K2 D2M8K2.u8306 = [0, 1065918058126, 3272525164488, 2393599540839, 397878506336, 14158861562, 0, 0] := by
  rw [show D2M8K2.u8306 = KTree.node D2M8K2.u8302 (nat_lit 18073352) (nat_lit 3021629160) (nat_lit 0) D2M8K2.u8305 from rfl, totK_node, atot8302, atot8305]
  decide +kernel

theorem arows8313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8313 = true := by
  rw [show D2M8K2.u8313 = KTree.node D2M8K2.u8309 (nat_lit 18082406) (nat_lit 3045237965) (nat_lit 0) D2M8K2.u8312 from rfl, allE_node, arows8309, irow8313, arows8312]
  all_goals rfl

theorem atot8313 : totK PD2M8K2 D2M8K2.u8313 = [576001265953, 2248861252125, 2833825318775, 1334213063987, 173125672591, 3667207281, 0, 0] := by
  rw [show D2M8K2.u8313 = KTree.node D2M8K2.u8309 (nat_lit 18082406) (nat_lit 3045237965) (nat_lit 0) D2M8K2.u8312 from rfl, totK_node, atot8309, atot8312]
  decide +kernel

theorem arows8324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8324 = true := by
  rw [show D2M8K2.u8324 = KTree.node D2M8K2.u8320 (nat_lit 18089450) (nat_lit 4191348247) (nat_lit 0) D2M8K2.u8323 from rfl, allE_node, arows8320, irow8324, arows8323]
  all_goals rfl

theorem atot8324 : totK PD2M8K2 D2M8K2.u8324 = [809638625193, 2792885266839, 2762381432556, 785392803937, 43748655635, 0, 0, 0] := by
  rw [show D2M8K2.u8324 = KTree.node D2M8K2.u8320 (nat_lit 18089450) (nat_lit 4191348247) (nat_lit 0) D2M8K2.u8323 from rfl, totK_node, atot8320, atot8323]
  decide +kernel

theorem arows8331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8331 = true := by
  rw [show D2M8K2.u8331 = KTree.node D2M8K2.u8327 (nat_lit 18096349) (nat_lit 1150417978) (nat_lit 0) D2M8K2.u8330 from rfl, allE_node, arows8327, irow8331, arows8330]
  all_goals rfl

theorem atot8331 : totK PD2M8K2 D2M8K2.u8331 = [592272587397, 2644774609161, 3119573066538, 784601815685, 29157448549, 0, 0, 0] := by
  rw [show D2M8K2.u8331 = KTree.node D2M8K2.u8327 (nat_lit 18096349) (nat_lit 1150417978) (nat_lit 0) D2M8K2.u8330 from rfl, totK_node, atot8327, atot8330]
  decide +kernel

theorem arows8339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8339 = true := by
  rw [show D2M8K2.u8339 = KTree.node D2M8K2.u8335 (nat_lit 18107390) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u8338 from rfl, allE_node, arows8335, irow8339, arows8338]
  all_goals rfl

theorem atot8339 : totK PD2M8K2 D2M8K2.u8339 = [0, 1240470359898, 3575211321769, 2123597669189, 190124003438, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8339 = KTree.node D2M8K2.u8335 (nat_lit 18107390) (nat_lit 2979313159) (nat_lit 0) D2M8K2.u8338 from rfl, totK_node, atot8335, atot8338]
  decide +kernel

theorem arows8346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8346 = true := by
  rw [show D2M8K2.u8346 = KTree.node D2M8K2.u8342 (nat_lit 18119328) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u8345 from rfl, allE_node, arows8342, irow8346, arows8345]
  all_goals rfl

theorem atot8346 : totK PD2M8K2 D2M8K2.u8346 = [439315660877, 1965820561937, 2927176819826, 1542792773083, 229925721251, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8346 = KTree.node D2M8K2.u8342 (nat_lit 18119328) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u8345 from rfl, totK_node, atot8342, atot8345]
  decide +kernel

theorem arows8355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8355 = true := by
  rw [show D2M8K2.u8355 = KTree.node D2M8K2.u8351 (nat_lit 18130376) (nat_lit 3551712602) (nat_lit 0) D2M8K2.u8354 from rfl, allE_node, arows8351, irow8355, arows8354]
  all_goals rfl

theorem atot8355 : totK PD2M8K2 D2M8K2.u8355 = [810518315638, 2799653600322, 2783223961660, 809291574701, 47907768652, 0, 0, 0] := by
  rw [show D2M8K2.u8355 = KTree.node D2M8K2.u8351 (nat_lit 18130376) (nat_lit 3551712602) (nat_lit 0) D2M8K2.u8354 from rfl, totK_node, atot8351, atot8354]
  decide +kernel

theorem arows8362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8362 = true := by
  rw [show D2M8K2.u8362 = KTree.node D2M8K2.u8358 (nat_lit 18140819) (nat_lit 2909699377) (nat_lit 0) D2M8K2.u8361 from rfl, allE_node, arows8358, irow8362, arows8361]
  all_goals rfl

theorem atot8362 : totK PD2M8K2 D2M8K2.u8362 = [739233179752, 2778083541826, 2958694661949, 740481584550, 24187886951, 0, 0, 0] := by
  rw [show D2M8K2.u8362 = KTree.node D2M8K2.u8358 (nat_lit 18140819) (nat_lit 2909699377) (nat_lit 0) D2M8K2.u8361 from rfl, totK_node, atot8358, atot8361]
  decide +kernel

theorem arows8370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8370 = true := by
  rw [show D2M8K2.u8370 = KTree.node D2M8K2.u8366 (nat_lit 18147882) (nat_lit 3802510447) (nat_lit 0) D2M8K2.u8369 from rfl, allE_node, arows8366, irow8370, arows8369]
  all_goals rfl

theorem atot8370 : totK PD2M8K2 D2M8K2.u8370 = [0, 1130379794492, 3419688685398, 2381958171284, 242437290153, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8370 = KTree.node D2M8K2.u8366 (nat_lit 18147882) (nat_lit 3802510447) (nat_lit 0) D2M8K2.u8369 from rfl, totK_node, atot8366, atot8369]
  decide +kernel

theorem arows8377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8377 = true := by
  rw [show D2M8K2.u8377 = KTree.node D2M8K2.u8373 (nat_lit 18156467) (nat_lit 2700065295) (nat_lit 0) D2M8K2.u8376 from rfl, allE_node, arows8373, irow8377, arows8376]
  all_goals rfl

theorem atot8377 : totK PD2M8K2 D2M8K2.u8377 = [0, 851767363465, 3030013195013, 2765364129954, 495578550399, 11053383638, 0, 0] := by
  rw [show D2M8K2.u8377 = KTree.node D2M8K2.u8373 (nat_lit 18156467) (nat_lit 2700065295) (nat_lit 0) D2M8K2.u8376 from rfl, totK_node, atot8373, atot8376]
  decide +kernel

theorem arows8387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8387 = true := by
  rw [show D2M8K2.u8387 = KTree.node D2M8K2.u8383 (nat_lit 18166567) (nat_lit 2331864838) (nat_lit 0) D2M8K2.u8386 from rfl, allE_node, arows8383, irow8387, arows8386]
  all_goals rfl

theorem atot8387 : totK PD2M8K2 D2M8K2.u8387 = [0, 839262315782, 2969459018399, 2733326543814, 568784578065, 23042499518, 0, 0] := by
  rw [show D2M8K2.u8387 = KTree.node D2M8K2.u8383 (nat_lit 18166567) (nat_lit 2331864838) (nat_lit 0) D2M8K2.u8386 from rfl, totK_node, atot8383, atot8386]
  decide +kernel

theorem arows8394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8394 = true := by
  rw [show D2M8K2.u8394 = KTree.node D2M8K2.u8390 (nat_lit 18177165) (nat_lit 1328051588) (nat_lit 0) D2M8K2.u8393 from rfl, allE_node, arows8390, irow8394, arows8393]
  all_goals rfl

theorem atot8394 : totK PD2M8K2 D2M8K2.u8394 = [0, 830622919361, 2892850319228, 2749188750151, 574355987649, 25916223298, 0, 0] := by
  rw [show D2M8K2.u8394 = KTree.node D2M8K2.u8390 (nat_lit 18177165) (nat_lit 1328051588) (nat_lit 0) D2M8K2.u8393 from rfl, totK_node, atot8390, atot8393]
  decide +kernel

theorem arows8402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8402 = true := by
  rw [show D2M8K2.u8402 = KTree.node D2M8K2.u8398 (nat_lit 18184084) (nat_lit 3999332539) (nat_lit 0) D2M8K2.u8401 from rfl, allE_node, arows8398, irow8402, arows8401]
  all_goals rfl

theorem atot8402 : totK PD2M8K2 D2M8K2.u8402 = [0, 417516665105, 2237937474907, 3262683729719, 1082602037601, 66795802044, 0, 0] := by
  rw [show D2M8K2.u8402 = KTree.node D2M8K2.u8398 (nat_lit 18184084) (nat_lit 3999332539) (nat_lit 0) D2M8K2.u8401 from rfl, totK_node, atot8398, atot8401]
  decide +kernel

theorem arows8409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8409 = true := by
  rw [show D2M8K2.u8409 = KTree.node D2M8K2.u8405 (nat_lit 18196777) (nat_lit 1505808569) (nat_lit 0) D2M8K2.u8408 from rfl, allE_node, arows8405, irow8409, arows8408]
  all_goals rfl

theorem atot8409 : totK PD2M8K2 D2M8K2.u8409 = [0, 0, 1388198516555, 3605095238416, 1796384290515, 190881903691, 1369150432, 0] := by
  rw [show D2M8K2.u8409 = KTree.node D2M8K2.u8405 (nat_lit 18196777) (nat_lit 1505808569) (nat_lit 0) D2M8K2.u8408 from rfl, totK_node, atot8405, atot8408]
  decide +kernel

theorem arows8418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8418 = true := by
  rw [show D2M8K2.u8418 = KTree.node D2M8K2.u8414 (nat_lit 18249624) (nat_lit 3570892849) (nat_lit 0) D2M8K2.u8417 from rfl, allE_node, arows8414, irow8418, arows8417]
  all_goals rfl

theorem atot8418 : totK PD2M8K2 D2M8K2.u8418 = [0, 843825529535, 2948241252119, 2744875989442, 581822061802, 23588783634, 0, 0] := by
  rw [show D2M8K2.u8418 = KTree.node D2M8K2.u8414 (nat_lit 18249624) (nat_lit 3570892849) (nat_lit 0) D2M8K2.u8417 from rfl, totK_node, atot8414, atot8417]
  decide +kernel

theorem arows8425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8425 = true := by
  rw [show D2M8K2.u8425 = KTree.node D2M8K2.u8421 (nat_lit 18263623) (nat_lit 2254195407) (nat_lit 0) D2M8K2.u8424 from rfl, allE_node, arows8421, irow8425, arows8424]
  all_goals rfl

theorem atot8425 : totK PD2M8K2 D2M8K2.u8425 = [0, 799555841750, 2932686584629, 2840670842511, 569348253763, 18035075282, 0, 0] := by
  rw [show D2M8K2.u8425 = KTree.node D2M8K2.u8421 (nat_lit 18263623) (nat_lit 2254195407) (nat_lit 0) D2M8K2.u8424 from rfl, totK_node, atot8421, atot8424]
  decide +kernel

theorem arows8433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8433 = true := by
  rw [show D2M8K2.u8433 = KTree.node D2M8K2.u8429 (nat_lit 18291790) (nat_lit 3684813496) (nat_lit 0) D2M8K2.u8432 from rfl, allE_node, arows8429, irow8433, arows8432]
  all_goals rfl

theorem atot8433 : totK PD2M8K2 D2M8K2.u8433 = [0, 766251667472, 2896605249538, 2930576640481, 616900690546, 19169862020, 0, 0] := by
  rw [show D2M8K2.u8433 = KTree.node D2M8K2.u8429 (nat_lit 18291790) (nat_lit 3684813496) (nat_lit 0) D2M8K2.u8432 from rfl, totK_node, atot8429, atot8432]
  decide +kernel

theorem arows8440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8440 = true := by
  rw [show D2M8K2.u8440 = KTree.node D2M8K2.u8436 (nat_lit 18302656) (nat_lit 1504160494) (nat_lit 0) D2M8K2.u8439 from rfl, allE_node, arows8436, irow8440, arows8439]
  all_goals rfl

theorem atot8440 : totK PD2M8K2 D2M8K2.u8440 = [0, 849235680180, 3012010807449, 2811081996744, 525343098873, 15336593870, 0, 0] := by
  rw [show D2M8K2.u8440 = KTree.node D2M8K2.u8436 (nat_lit 18302656) (nat_lit 1504160494) (nat_lit 0) D2M8K2.u8439 from rfl, totK_node, atot8436, atot8439]
  decide +kernel

theorem arows8452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8452 = true := by
  rw [show D2M8K2.u8452 = KTree.node D2M8K2.u8448 (nat_lit 18309748) (nat_lit 3271116645) (nat_lit 0) D2M8K2.u8451 from rfl, allE_node, arows8448, irow8452, arows8451]
  all_goals rfl

theorem atot8452 : totK PD2M8K2 D2M8K2.u8452 = [0, 857733418514, 2984992476663, 2763379924075, 548900156894, 17835583175, 0, 0] := by
  rw [show D2M8K2.u8452 = KTree.node D2M8K2.u8448 (nat_lit 18309748) (nat_lit 3271116645) (nat_lit 0) D2M8K2.u8451 from rfl, totK_node, atot8448, atot8451]
  decide +kernel

theorem arows8459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8459 = true := by
  rw [show D2M8K2.u8459 = KTree.node D2M8K2.u8455 (nat_lit 18338239) (nat_lit 746999778) (nat_lit 0) D2M8K2.u8458 from rfl, allE_node, arows8455, irow8459, arows8458]
  all_goals rfl

theorem atot8459 : totK PD2M8K2 D2M8K2.u8459 = [0, 939107500834, 3078645655923, 2675555474602, 492523968965, 14393010609, 0, 0] := by
  rw [show D2M8K2.u8459 = KTree.node D2M8K2.u8455 (nat_lit 18338239) (nat_lit 746999778) (nat_lit 0) D2M8K2.u8458 from rfl, totK_node, atot8455, atot8458]
  decide +kernel

theorem arows8467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8467 = true := by
  rw [show D2M8K2.u8467 = KTree.node D2M8K2.u8463 (nat_lit 18345180) (nat_lit 3141604827) (nat_lit 0) D2M8K2.u8466 from rfl, allE_node, arows8463, irow8467, arows8466]
  all_goals rfl

theorem atot8467 : totK PD2M8K2 D2M8K2.u8467 = [0, 851461518006, 2994759447732, 2767114945593, 537041809108, 18164832359, 0, 0] := by
  rw [show D2M8K2.u8467 = KTree.node D2M8K2.u8463 (nat_lit 18345180) (nat_lit 3141604827) (nat_lit 0) D2M8K2.u8466 from rfl, totK_node, atot8463, atot8466]
  decide +kernel

theorem arows8474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8474 = true := by
  rw [show D2M8K2.u8474 = KTree.node D2M8K2.u8470 (nat_lit 18377054) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u8473 from rfl, allE_node, arows8470, irow8474, arows8473]
  all_goals rfl

theorem atot8474 : totK PD2M8K2 D2M8K2.u8474 = [0, 872198209827, 3047003775416, 2800235714776, 521665549699, 10944778055, 0, 0] := by
  rw [show D2M8K2.u8474 = KTree.node D2M8K2.u8470 (nat_lit 18377054) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u8473 from rfl, totK_node, atot8470, atot8473]
  decide +kernel

theorem arows8483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8483 = true := by
  rw [show D2M8K2.u8483 = KTree.node D2M8K2.u8479 (nat_lit 18384315) (nat_lit 2926314110) (nat_lit 0) D2M8K2.u8482 from rfl, allE_node, arows8479, irow8483, arows8482]
  all_goals rfl

theorem atot8483 : totK PD2M8K2 D2M8K2.u8483 = [0, 853481961918, 3049876210841, 2842292160649, 507526758095, 10331839290, 0, 0] := by
  rw [show D2M8K2.u8483 = KTree.node D2M8K2.u8479 (nat_lit 18384315) (nat_lit 2926314110) (nat_lit 0) D2M8K2.u8482 from rfl, totK_node, atot8479, atot8482]
  decide +kernel

theorem arows8490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8490 = true := by
  rw [show D2M8K2.u8490 = KTree.node D2M8K2.u8486 (nat_lit 18459987) (nat_lit 3652879915) (nat_lit 0) D2M8K2.u8489 from rfl, allE_node, arows8486, irow8490, arows8489]
  all_goals rfl

theorem atot8490 : totK PD2M8K2 D2M8K2.u8490 = [682467312879, 2166327588901, 2441856933485, 1557315443706, 417745335594, 21897291087, 0, 0] := by
  rw [show D2M8K2.u8490 = KTree.node D2M8K2.u8486 (nat_lit 18459987) (nat_lit 3652879915) (nat_lit 0) D2M8K2.u8489 from rfl, totK_node, atot8486, atot8489]
  decide +kernel

theorem arows8498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8498 = true := by
  rw [show D2M8K2.u8498 = KTree.node D2M8K2.u8494 (nat_lit 18466451) (nat_lit 2727601205) (nat_lit 0) D2M8K2.u8497 from rfl, allE_node, arows8494, irow8498, arows8497]
  all_goals rfl

theorem atot8498 : totK PD2M8K2 D2M8K2.u8498 = [820666276709, 2879453429221, 2834384456439, 646696057820, 24860209971, 0, 0, 0] := by
  rw [show D2M8K2.u8498 = KTree.node D2M8K2.u8494 (nat_lit 18466451) (nat_lit 2727601205) (nat_lit 0) D2M8K2.u8497 from rfl, totK_node, atot8494, atot8497]
  decide +kernel

theorem arows8505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8505 = true := by
  rw [show D2M8K2.u8505 = KTree.node D2M8K2.u8501 (nat_lit 18473060) (nat_lit 1743135235) (nat_lit 0) D2M8K2.u8504 from rfl, allE_node, arows8501, irow8505, arows8504]
  all_goals rfl

theorem atot8505 : totK PD2M8K2 D2M8K2.u8505 = [614600734004, 2664264578813, 3044682390366, 850128709483, 48868849255, 0, 0, 0] := by
  rw [show D2M8K2.u8505 = KTree.node D2M8K2.u8501 (nat_lit 18473060) (nat_lit 1743135235) (nat_lit 0) D2M8K2.u8504 from rfl, totK_node, atot8501, atot8504]
  decide +kernel

theorem arows8515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8515 = true := by
  rw [show D2M8K2.u8515 = KTree.node D2M8K2.u8511 (nat_lit 18482674) (nat_lit 4147043252) (nat_lit 0) D2M8K2.u8514 from rfl, allE_node, arows8511, irow8515, arows8514]
  all_goals rfl

theorem atot8515 : totK PD2M8K2 D2M8K2.u8515 = [0, 742177202189, 2758420925897, 2866583107318, 797214880659, 42081742489, 0, 0] := by
  rw [show D2M8K2.u8515 = KTree.node D2M8K2.u8511 (nat_lit 18482674) (nat_lit 4147043252) (nat_lit 0) D2M8K2.u8514 from rfl, totK_node, atot8511, atot8514]
  decide +kernel

theorem arows8522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8522 = true := by
  rw [show D2M8K2.u8522 = KTree.node D2M8K2.u8518 (nat_lit 18489842) (nat_lit 3169751159) (nat_lit 0) D2M8K2.u8521 from rfl, allE_node, arows8518, irow8522, arows8521]
  all_goals rfl

theorem atot8522 : totK PD2M8K2 D2M8K2.u8522 = [0, 927222558999, 3165837239583, 2690302420584, 431992406585, 6634014755, 0, 0] := by
  rw [show D2M8K2.u8522 = KTree.node D2M8K2.u8518 (nat_lit 18489842) (nat_lit 3169751159) (nat_lit 0) D2M8K2.u8521 from rfl, totK_node, atot8518, atot8521]
  decide +kernel

theorem arows8530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8530 = true := by
  rw [show D2M8K2.u8530 = KTree.node D2M8K2.u8526 (nat_lit 18500531) (nat_lit 2951562183) (nat_lit 0) D2M8K2.u8529 from rfl, allE_node, arows8526, irow8530, arows8529]
  all_goals rfl

theorem atot8530 : totK PD2M8K2 D2M8K2.u8530 = [429522638084, 1798420139045, 2811174135458, 1856357026034, 351213424525, 9302370699, 0, 0] := by
  rw [show D2M8K2.u8530 = KTree.node D2M8K2.u8526 (nat_lit 18500531) (nat_lit 2951562183) (nat_lit 0) D2M8K2.u8529 from rfl, totK_node, atot8526, atot8529]
  decide +kernel

theorem arows8537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8537 = true := by
  rw [show D2M8K2.u8537 = KTree.node D2M8K2.u8533 (nat_lit 18506480) (nat_lit 3691776655) (nat_lit 0) D2M8K2.u8536 from rfl, allE_node, arows8533, irow8537, arows8536]
  all_goals rfl

theorem atot8537 : totK PD2M8K2 D2M8K2.u8537 = [826728102901, 2936413165032, 2812300532032, 620405220325, 22016016005, 0, 0, 0] := by
  rw [show D2M8K2.u8537 = KTree.node D2M8K2.u8533 (nat_lit 18506480) (nat_lit 3691776655) (nat_lit 0) D2M8K2.u8536 from rfl, totK_node, atot8533, atot8536]
  decide +kernel

theorem arows8546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8546 = true := by
  rw [show D2M8K2.u8546 = KTree.node D2M8K2.u8542 (nat_lit 18517029) (nat_lit 896307221) (nat_lit 0) D2M8K2.u8545 from rfl, allE_node, arows8542, irow8546, arows8545]
  all_goals rfl

theorem atot8546 : totK PD2M8K2 D2M8K2.u8546 = [405776974296, 2130599449539, 3292219952981, 1360774252948, 90796715846, 0, 0, 0] := by
  rw [show D2M8K2.u8546 = KTree.node D2M8K2.u8542 (nat_lit 18517029) (nat_lit 896307221) (nat_lit 0) D2M8K2.u8545 from rfl, totK_node, atot8542, atot8545]
  decide +kernel

theorem arows8553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8553 = true := by
  rw [show D2M8K2.u8553 = KTree.node D2M8K2.u8549 (nat_lit 18531852) (nat_lit 3030158248) (nat_lit 0) D2M8K2.u8552 from rfl, allE_node, arows8549, irow8553, arows8552]
  all_goals rfl

theorem atot8553 : totK PD2M8K2 D2M8K2.u8553 = [0, 884399194900, 3074127596810, 2595153368329, 488623191010, 17590593026, 0, 0] := by
  rw [show D2M8K2.u8553 = KTree.node D2M8K2.u8549 (nat_lit 18531852) (nat_lit 3030158248) (nat_lit 0) D2M8K2.u8552 from rfl, totK_node, atot8549, atot8552]
  decide +kernel

theorem arows8561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8561 = true := by
  rw [show D2M8K2.u8561 = KTree.node D2M8K2.u8557 (nat_lit 18541947) (nat_lit 3688517945) (nat_lit 0) D2M8K2.u8560 from rfl, allE_node, arows8557, irow8561, arows8560]
  all_goals rfl

theorem atot8561 : totK PD2M8K2 D2M8K2.u8561 = [772198506418, 2803009088012, 2855881778794, 817247594686, 45717124287, 0, 0, 0] := by
  rw [show D2M8K2.u8561 = KTree.node D2M8K2.u8557 (nat_lit 18541947) (nat_lit 3688517945) (nat_lit 0) D2M8K2.u8560 from rfl, totK_node, atot8557, atot8560]
  decide +kernel

theorem arows8568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8568 = true := by
  rw [show D2M8K2.u8568 = KTree.node D2M8K2.u8564 (nat_lit 18551276) (nat_lit 3765692127) (nat_lit 0) D2M8K2.u8567 from rfl, allE_node, arows8564, irow8568, arows8567]
  all_goals rfl

theorem atot8568 : totK PD2M8K2 D2M8K2.u8568 = [853379733753, 2978015902478, 2799090120494, 603890075426, 21146926224, 0, 0, 0] := by
  rw [show D2M8K2.u8568 = KTree.node D2M8K2.u8564 (nat_lit 18551276) (nat_lit 3765692127) (nat_lit 0) D2M8K2.u8567 from rfl, totK_node, atot8564, atot8567]
  decide +kernel

theorem arows8579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8579 = true := by
  rw [show D2M8K2.u8579 = KTree.node D2M8K2.u8575 (nat_lit 18557954) (nat_lit 3871635984) (nat_lit 0) D2M8K2.u8578 from rfl, allE_node, arows8575, irow8579, arows8578]
  all_goals rfl

theorem atot8579 : totK PD2M8K2 D2M8K2.u8579 = [417183842111, 2010873238615, 3109762155718, 1506781491698, 144282238372, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8579 = KTree.node D2M8K2.u8575 (nat_lit 18557954) (nat_lit 3871635984) (nat_lit 0) D2M8K2.u8578 from rfl, totK_node, atot8575, atot8578]
  decide +kernel

theorem arows8586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8586 = true := by
  rw [show D2M8K2.u8586 = KTree.node D2M8K2.u8582 (nat_lit 18570494) (nat_lit 2850828212) (nat_lit 0) D2M8K2.u8585 from rfl, allE_node, arows8582, irow8586, arows8585]
  all_goals rfl

theorem atot8586 : totK PD2M8K2 D2M8K2.u8586 = [0, 1095824625988, 3317641930165, 2389363666369, 386499410424, 13105450397, 0, 0] := by
  rw [show D2M8K2.u8586 = KTree.node D2M8K2.u8582 (nat_lit 18570494) (nat_lit 2850828212) (nat_lit 0) D2M8K2.u8585 from rfl, totK_node, atot8582, atot8585]
  decide +kernel

theorem arows8594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8594 = true := by
  rw [show D2M8K2.u8594 = KTree.node D2M8K2.u8590 (nat_lit 18577566) (nat_lit 3929778058) (nat_lit 0) D2M8K2.u8593 from rfl, allE_node, arows8590, irow8594, arows8593]
  all_goals rfl

theorem atot8594 : totK PD2M8K2 D2M8K2.u8594 = [502750546267, 2032439985153, 2867906941968, 1550906533560, 208790379487, 4720618446, 0, 0] := by
  rw [show D2M8K2.u8594 = KTree.node D2M8K2.u8590 (nat_lit 18577566) (nat_lit 3929778058) (nat_lit 0) D2M8K2.u8593 from rfl, totK_node, atot8590, atot8593]
  decide +kernel

theorem arows8601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8601 = true := by
  rw [show D2M8K2.u8601 = KTree.node D2M8K2.u8597 (nat_lit 18586438) (nat_lit 3147735141) (nat_lit 0) D2M8K2.u8600 from rfl, allE_node, arows8597, irow8601, arows8600]
  all_goals rfl

theorem atot8601 : totK PD2M8K2 D2M8K2.u8601 = [710616226373, 2645576761728, 2881358308870, 908083870137, 50651435456, 0, 0, 0] := by
  rw [show D2M8K2.u8601 = KTree.node D2M8K2.u8597 (nat_lit 18586438) (nat_lit 3147735141) (nat_lit 0) D2M8K2.u8600 from rfl, totK_node, atot8597, atot8600]
  decide +kernel

theorem arows8610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8610 = true := by
  rw [show D2M8K2.u8610 = KTree.node D2M8K2.u8606 (nat_lit 18593377) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u8609 from rfl, allE_node, arows8606, irow8610, arows8609]
  all_goals rfl

theorem atot8610 : totK PD2M8K2 D2M8K2.u8610 = [774117690643, 2937874047773, 2897204035018, 604041736205, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u8610 = KTree.node D2M8K2.u8606 (nat_lit 18593377) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u8609 from rfl, totK_node, atot8606, atot8609]
  decide +kernel

theorem arows8617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8617 = true := by
  rw [show D2M8K2.u8617 = KTree.node D2M8K2.u8613 (nat_lit 18604728) (nat_lit 3220007670) (nat_lit 0) D2M8K2.u8616 from rfl, allE_node, arows8613, irow8617, arows8616]
  all_goals rfl

theorem atot8617 : totK PD2M8K2 D2M8K2.u8617 = [0, 1264070878003, 3579665272663, 2117628851128, 191905093383, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8617 = KTree.node D2M8K2.u8613 (nat_lit 18604728) (nat_lit 3220007670) (nat_lit 0) D2M8K2.u8616 from rfl, totK_node, atot8613, atot8616]
  decide +kernel

theorem arows8625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8625 = true := by
  rw [show D2M8K2.u8625 = KTree.node D2M8K2.u8621 (nat_lit 18615985) (nat_lit 1423666189) (nat_lit 0) D2M8K2.u8624 from rfl, allE_node, arows8621, irow8625, arows8624]
  all_goals rfl

theorem atot8625 : totK PD2M8K2 D2M8K2.u8625 = [326853619374, 1788032923698, 3071858442918, 1722050109215, 242241910704, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8625 = KTree.node D2M8K2.u8621 (nat_lit 18615985) (nat_lit 1423666189) (nat_lit 0) D2M8K2.u8624 from rfl, totK_node, atot8621, atot8624]
  decide +kernel

theorem arows8632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8632 = true := by
  rw [show D2M8K2.u8632 = KTree.node D2M8K2.u8628 (nat_lit 18627243) (nat_lit 3454441189) (nat_lit 0) D2M8K2.u8631 from rfl, allE_node, arows8628, irow8632, arows8631]
  all_goals rfl

theorem atot8632 : totK PD2M8K2 D2M8K2.u8632 = [814752306602, 2803703049046, 2825609948496, 802305439761, 39899052951, 0, 0, 0] := by
  rw [show D2M8K2.u8632 = KTree.node D2M8K2.u8628 (nat_lit 18627243) (nat_lit 3454441189) (nat_lit 0) D2M8K2.u8631 from rfl, totK_node, atot8628, atot8631]
  decide +kernel

theorem arows8642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8642 = true := by
  rw [show D2M8K2.u8642 = KTree.node D2M8K2.u8638 (nat_lit 18634116) (nat_lit 3046544567) (nat_lit 0) D2M8K2.u8641 from rfl, allE_node, arows8638, irow8642, arows8641]
  all_goals rfl

theorem atot8642 : totK PD2M8K2 D2M8K2.u8642 = [857731848908, 2983244307873, 2799033975973, 612679138714, 22866299895, 0, 0, 0] := by
  rw [show D2M8K2.u8642 = KTree.node D2M8K2.u8638 (nat_lit 18634116) (nat_lit 3046544567) (nat_lit 0) D2M8K2.u8641 from rfl, totK_node, atot8638, atot8641]
  decide +kernel

theorem arows8649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8649 = true := by
  rw [show D2M8K2.u8649 = KTree.node D2M8K2.u8645 (nat_lit 18644882) (nat_lit 3655141673) (nat_lit 0) D2M8K2.u8648 from rfl, allE_node, arows8645, irow8649, arows8648]
  all_goals rfl

theorem atot8649 : totK PD2M8K2 D2M8K2.u8649 = [0, 1243692677448, 3515874278731, 2234024473670, 225460803207, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8649 = KTree.node D2M8K2.u8645 (nat_lit 18644882) (nat_lit 3655141673) (nat_lit 0) D2M8K2.u8648 from rfl, totK_node, atot8645, atot8648]
  decide +kernel

theorem arows8657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8657 = true := by
  rw [show D2M8K2.u8657 = KTree.node D2M8K2.u8653 (nat_lit 18653544) (nat_lit 3534038886) (nat_lit 0) D2M8K2.u8656 from rfl, allE_node, arows8653, irow8657, arows8656]
  all_goals rfl

theorem atot8657 : totK PD2M8K2 D2M8K2.u8657 = [0, 960824769669, 3197434996942, 2602652534925, 422320037778, 9811245038, 0, 0] := by
  rw [show D2M8K2.u8657 = KTree.node D2M8K2.u8653 (nat_lit 18653544) (nat_lit 3534038886) (nat_lit 0) D2M8K2.u8656 from rfl, totK_node, atot8653, atot8656]
  decide +kernel

theorem arows8664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8664 = true := by
  rw [show D2M8K2.u8664 = KTree.node D2M8K2.u8660 (nat_lit 18708574) (nat_lit 3156468113) (nat_lit 0) D2M8K2.u8663 from rfl, allE_node, arows8660, irow8664, arows8663]
  all_goals rfl

theorem atot8664 : totK PD2M8K2 D2M8K2.u8664 = [0, 615300261985, 2506100024327, 3045488958963, 1014713623717, 59360566171, 0, 0] := by
  rw [show D2M8K2.u8664 = KTree.node D2M8K2.u8660 (nat_lit 18708574) (nat_lit 3156468113) (nat_lit 0) D2M8K2.u8663 from rfl, totK_node, atot8660, atot8663]
  decide +kernel

theorem arows8673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8673 = true := by
  rw [show D2M8K2.u8673 = KTree.node D2M8K2.u8669 (nat_lit 18715114) (nat_lit 3828936700) (nat_lit 0) D2M8K2.u8672 from rfl, allE_node, arows8669, irow8673, arows8672]
  all_goals rfl

theorem atot8673 : totK PD2M8K2 D2M8K2.u8673 = [0, 813959638337, 2918039162855, 2812458965587, 624946862521, 17530736909, 0, 0] := by
  rw [show D2M8K2.u8673 = KTree.node D2M8K2.u8669 (nat_lit 18715114) (nat_lit 3828936700) (nat_lit 0) D2M8K2.u8672 from rfl, totK_node, atot8669, atot8672]
  decide +kernel

theorem arows8680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8680 = true := by
  rw [show D2M8K2.u8680 = KTree.node D2M8K2.u8676 (nat_lit 18721755) (nat_lit 3746109792) (nat_lit 0) D2M8K2.u8679 from rfl, allE_node, arows8676, irow8680, arows8679]
  all_goals rfl

theorem atot8680 : totK PD2M8K2 D2M8K2.u8680 = [0, 685208091616, 2713532231791, 2978048118561, 798878599885, 35715461096, 0, 0] := by
  rw [show D2M8K2.u8680 = KTree.node D2M8K2.u8676 (nat_lit 18721755) (nat_lit 3746109792) (nat_lit 0) D2M8K2.u8679 from rfl, totK_node, atot8676, atot8679]
  decide +kernel

theorem arows8688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8688 = true := by
  rw [show D2M8K2.u8688 = KTree.node D2M8K2.u8684 (nat_lit 18731324) (nat_lit 2573832925) (nat_lit 0) D2M8K2.u8687 from rfl, allE_node, arows8684, irow8688, arows8687]
  all_goals rfl

theorem atot8688 : totK PD2M8K2 D2M8K2.u8688 = [0, 0, 755023301456, 2743137528349, 2847992316991, 777486174466, 41989737272, 0] := by
  rw [show D2M8K2.u8688 = KTree.node D2M8K2.u8684 (nat_lit 18731324) (nat_lit 2573832925) (nat_lit 0) D2M8K2.u8687 from rfl, totK_node, atot8684, atot8687]
  decide +kernel

theorem arows8695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8695 = true := by
  rw [show D2M8K2.u8695 = KTree.node D2M8K2.u8691 (nat_lit 18738624) (nat_lit 2577070208) (nat_lit 0) D2M8K2.u8694 from rfl, allE_node, arows8691, irow8695, arows8694]
  all_goals rfl

theorem atot8695 : totK PD2M8K2 D2M8K2.u8695 = [0, 0, 983257446104, 3194240444927, 2581891703505, 384544347490, 6518567072, 0] := by
  rw [show D2M8K2.u8695 = KTree.node D2M8K2.u8691 (nat_lit 18738624) (nat_lit 2577070208) (nat_lit 0) D2M8K2.u8694 from rfl, totK_node, atot8691, atot8694]
  decide +kernel

theorem arows8708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8708 = true := by
  rw [show D2M8K2.u8708 = KTree.node D2M8K2.u8704 (nat_lit 18749408) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u8707 from rfl, allE_node, arows8704, irow8708, arows8707]
  all_goals rfl

theorem atot8708 : totK PD2M8K2 D2M8K2.u8708 = [0, 429522638084, 1794789747167, 2809741984522, 1831709852990, 324904286388, 9139067247, 0] := by
  rw [show D2M8K2.u8708 = KTree.node D2M8K2.u8704 (nat_lit 18749408) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u8707 from rfl, totK_node, atot8704, atot8707]
  decide +kernel

theorem arows8715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8715 = true := by
  rw [show D2M8K2.u8715 = KTree.node D2M8K2.u8711 (nat_lit 18755385) (nat_lit 1881068813) (nat_lit 0) D2M8K2.u8714 from rfl, allE_node, arows8711, irow8715, arows8714]
  all_goals rfl

theorem atot8715 : totK PD2M8K2 D2M8K2.u8715 = [0, 826728102901, 2934062750395, 2802993879598, 610937076468, 20786346519, 0, 0] := by
  rw [show D2M8K2.u8715 = KTree.node D2M8K2.u8711 (nat_lit 18755385) (nat_lit 1881068813) (nat_lit 0) D2M8K2.u8714 from rfl, totK_node, atot8711, atot8714]
  decide +kernel

theorem arows8723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8723 = true := by
  rw [show D2M8K2.u8723 = KTree.node D2M8K2.u8719 (nat_lit 18765941) (nat_lit 1757706780) (nat_lit 0) D2M8K2.u8722 from rfl, allE_node, arows8719, irow8723, arows8722]
  all_goals rfl

theorem atot8723 : totK PD2M8K2 D2M8K2.u8723 = [0, 405776974296, 2141896343571, 3252081886844, 1347923484509, 89717416738, 0, 0] := by
  rw [show D2M8K2.u8723 = KTree.node D2M8K2.u8719 (nat_lit 18765941) (nat_lit 1757706780) (nat_lit 0) D2M8K2.u8722 from rfl, totK_node, atot8719, atot8722]
  decide +kernel

theorem arows8730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8730 = true := by
  rw [show D2M8K2.u8730 = KTree.node D2M8K2.u8726 (nat_lit 18780942) (nat_lit 3866465331) (nat_lit 0) D2M8K2.u8729 from rfl, allE_node, arows8726, irow8730, arows8729]
  all_goals rfl

theorem atot8730 : totK PD2M8K2 D2M8K2.u8730 = [0, 32530458273, 993636970992, 3211325886140, 2497849235710, 354031166066, 6546549506, 0] := by
  rw [show D2M8K2.u8730 = KTree.node D2M8K2.u8726 (nat_lit 18780942) (nat_lit 3866465331) (nat_lit 0) D2M8K2.u8729 from rfl, totK_node, atot8726, atot8729]
  decide +kernel

theorem arows8739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8739 = true := by
  rw [show D2M8K2.u8739 = KTree.node D2M8K2.u8735 (nat_lit 18791219) (nat_lit 2850697850) (nat_lit 0) D2M8K2.u8738 from rfl, allE_node, arows8735, irow8739, arows8738]
  all_goals rfl

theorem atot8739 : totK PD2M8K2 D2M8K2.u8739 = [0, 822715377145, 2884401687748, 2767440580668, 734734017648, 38796216711, 0, 0] := by
  rw [show D2M8K2.u8739 = KTree.node D2M8K2.u8735 (nat_lit 18791219) (nat_lit 2850697850) (nat_lit 0) D2M8K2.u8738 from rfl, totK_node, atot8735, atot8738]
  decide +kernel

theorem arows8746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8746 = true := by
  rw [show D2M8K2.u8746 = KTree.node D2M8K2.u8742 (nat_lit 18800696) (nat_lit 3647455840) (nat_lit 0) D2M8K2.u8745 from rfl, allE_node, arows8742, irow8746, arows8745]
  all_goals rfl

theorem atot8746 : totK PD2M8K2 D2M8K2.u8746 = [0, 849183652507, 2963255425681, 2809325968356, 589864118792, 18176614947, 0, 0] := by
  rw [show D2M8K2.u8746 = KTree.node D2M8K2.u8742 (nat_lit 18800696) (nat_lit 3647455840) (nat_lit 0) D2M8K2.u8745 from rfl, totK_node, atot8742, atot8745]
  decide +kernel

theorem arows8754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8754 = true := by
  rw [show D2M8K2.u8754 = KTree.node D2M8K2.u8750 (nat_lit 18807498) (nat_lit 3360193961) (nat_lit 0) D2M8K2.u8753 from rfl, allE_node, arows8750, irow8754, arows8753]
  all_goals rfl

theorem atot8754 : totK PD2M8K2 D2M8K2.u8754 = [0, 338332594357, 2210151503163, 3390650787551, 1205987004830, 64859518252, 0, 0] := by
  rw [show D2M8K2.u8754 = KTree.node D2M8K2.u8750 (nat_lit 18807498) (nat_lit 3360193961) (nat_lit 0) D2M8K2.u8753 from rfl, totK_node, atot8750, atot8753]
  decide +kernel

theorem arows8761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8761 = true := by
  rw [show D2M8K2.u8761 = KTree.node D2M8K2.u8757 (nat_lit 18821571) (nat_lit 963012696) (nat_lit 0) D2M8K2.u8760 from rfl, allE_node, arows8757, irow8761, arows8760]
  all_goals rfl

theorem atot8761 : totK PD2M8K2 D2M8K2.u8761 = [0, 0, 946096565778, 3218455286611, 2572585348365, 368449497235, 6624648996, 0] := by
  rw [show D2M8K2.u8761 = KTree.node D2M8K2.u8757 (nat_lit 18821571) (nat_lit 963012696) (nat_lit 0) D2M8K2.u8760 from rfl, totK_node, atot8757, atot8760]
  decide +kernel

theorem arows8771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8771 = true := by
  rw [show D2M8K2.u8771 = KTree.node D2M8K2.u8767 (nat_lit 18831221) (nat_lit 2370913267) (nat_lit 0) D2M8K2.u8770 from rfl, allE_node, arows8767, irow8771, arows8770]
  all_goals rfl

theorem atot8771 : totK PD2M8K2 D2M8K2.u8771 = [0, 752171029482, 2735851109949, 2816266822040, 845247803724, 50489227236, 0, 0] := by
  rw [show D2M8K2.u8771 = KTree.node D2M8K2.u8767 (nat_lit 18831221) (nat_lit 2370913267) (nat_lit 0) D2M8K2.u8770 from rfl, totK_node, atot8767, atot8770]
  decide +kernel

theorem arows8778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8778 = true := by
  rw [show D2M8K2.u8778 = KTree.node D2M8K2.u8774 (nat_lit 18837708) (nat_lit 3029272719) (nat_lit 0) D2M8K2.u8777 from rfl, allE_node, arows8774, irow8778, arows8777]
  all_goals rfl

theorem atot8778 : totK PD2M8K2 D2M8K2.u8778 = [0, 799002660520, 2841278397148, 2819813983315, 697474811470, 23498345109, 0, 0] := by
  rw [show D2M8K2.u8778 = KTree.node D2M8K2.u8774 (nat_lit 18837708) (nat_lit 3029272719) (nat_lit 0) D2M8K2.u8777 from rfl, totK_node, atot8774, atot8777]
  decide +kernel

theorem arows8786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8786 = true := by
  rw [show D2M8K2.u8786 = KTree.node D2M8K2.u8782 (nat_lit 18844475) (nat_lit 2596172410) (nat_lit 0) D2M8K2.u8785 from rfl, allE_node, arows8782, irow8786, arows8785]
  all_goals rfl

theorem atot8786 : totK PD2M8K2 D2M8K2.u8786 = [0, 436310773281, 2308652314370, 3289389003840, 1059815001854, 55691954396, 0, 0] := by
  rw [show D2M8K2.u8786 = KTree.node D2M8K2.u8782 (nat_lit 18844475) (nat_lit 2596172410) (nat_lit 0) D2M8K2.u8785 from rfl, totK_node, atot8782, atot8785]
  decide +kernel

theorem arows8793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8793 = true := by
  rw [show D2M8K2.u8793 = KTree.node D2M8K2.u8789 (nat_lit 18860380) (nat_lit 2364595629) (nat_lit 0) D2M8K2.u8792 from rfl, allE_node, arows8789, irow8793, arows8792]
  all_goals rfl

theorem atot8793 : totK PD2M8K2 D2M8K2.u8793 = [0, 0, 1376384459225, 3706801597331, 1941913010844, 125003475509, 0, 0] := by
  rw [show D2M8K2.u8793 = KTree.node D2M8K2.u8789 (nat_lit 18860380) (nat_lit 2364595629) (nat_lit 0) D2M8K2.u8792 from rfl, totK_node, atot8789, atot8792]
  decide +kernel

theorem arows8802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8802 = true := by
  rw [show D2M8K2.u8802 = KTree.node D2M8K2.u8798 (nat_lit 18873674) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u8801 from rfl, allE_node, arows8798, irow8802, arows8801]
  all_goals rfl

theorem atot8802 : totK PD2M8K2 D2M8K2.u8802 = [0, 756224089258, 2616582560213, 2703400440800, 1019720015005, 132646306340, 1429815836, 0] := by
  rw [show D2M8K2.u8802 = KTree.node D2M8K2.u8798 (nat_lit 18873674) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u8801 from rfl, totK_node, atot8798, atot8801]
  decide +kernel

theorem arows8809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8809 = true := by
  rw [show D2M8K2.u8809 = KTree.node D2M8K2.u8805 (nat_lit 18879869) (nat_lit 2233364973) (nat_lit 0) D2M8K2.u8808 from rfl, allE_node, arows8805, irow8809, arows8808]
  all_goals rfl

theorem atot8809 : totK PD2M8K2 D2M8K2.u8809 = [0, 802344949957, 2849948049398, 2857143019645, 711745732925, 25053276113, 0, 0] := by
  rw [show D2M8K2.u8809 = KTree.node D2M8K2.u8805 (nat_lit 18879869) (nat_lit 2233364973) (nat_lit 0) D2M8K2.u8808 from rfl, totK_node, atot8805, atot8808]
  decide +kernel

theorem arows8817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8817 = true := by
  rw [show D2M8K2.u8817 = KTree.node D2M8K2.u8813 (nat_lit 18889725) (nat_lit 1427970396) (nat_lit 0) D2M8K2.u8816 from rfl, allE_node, arows8813, irow8817, arows8816]
  all_goals rfl

theorem atot8817 : totK PD2M8K2 D2M8K2.u8817 = [0, 440768735669, 2374113122597, 3289151084694, 1086420836158, 56902173374, 0, 0] := by
  rw [show D2M8K2.u8817 = KTree.node D2M8K2.u8813 (nat_lit 18889725) (nat_lit 1427970396) (nat_lit 0) D2M8K2.u8816 from rfl, totK_node, atot8813, atot8816]
  decide +kernel

theorem arows8824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8824 = true := by
  rw [show D2M8K2.u8824 = KTree.node D2M8K2.u8820 (nat_lit 18901205) (nat_lit 2177128948) (nat_lit 0) D2M8K2.u8823 from rfl, allE_node, arows8820, irow8824, arows8823]
  all_goals rfl

theorem atot8824 : totK PD2M8K2 D2M8K2.u8824 = [0, 0, 1016270557633, 3312647315321, 2559935982073, 307235258449, 2656098521, 0] := by
  rw [show D2M8K2.u8824 = KTree.node D2M8K2.u8820 (nat_lit 18901205) (nat_lit 2177128948) (nat_lit 0) D2M8K2.u8823 from rfl, totK_node, atot8820, atot8823]
  decide +kernel

theorem arows8835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8835 = true := by
  rw [show D2M8K2.u8835 = KTree.node D2M8K2.u8831 (nat_lit 19409740) (nat_lit 3902263508) (nat_lit 0) D2M8K2.u8834 from rfl, allE_node, arows8831, irow8835, arows8834]
  all_goals rfl

theorem atot8835 : totK PD2M8K2 D2M8K2.u8835 = [674487085575, 2048780291881, 1728235778021, 1226048851544, 1196302341409, 275600791882, 9533751846, 0] := by
  rw [show D2M8K2.u8835 = KTree.node D2M8K2.u8831 (nat_lit 19409740) (nat_lit 3902263508) (nat_lit 0) D2M8K2.u8834 from rfl, totK_node, atot8831, atot8834]
  decide +kernel

theorem arows8842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8842 = true := by
  rw [show D2M8K2.u8842 = KTree.node D2M8K2.u8838 (nat_lit 19420664) (nat_lit 3924363918) (nat_lit 0) D2M8K2.u8841 from rfl, allE_node, arows8838, irow8842, arows8841]
  all_goals rfl

theorem atot8842 : totK PD2M8K2 D2M8K2.u8842 = [826815419062, 2883692759093, 2765235336615, 642324943432, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u8842 = KTree.node D2M8K2.u8838 (nat_lit 19420664) (nat_lit 3924363918) (nat_lit 0) D2M8K2.u8841 from rfl, totK_node, atot8838, atot8841]
  decide +kernel

theorem arows8850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8850 = true := by
  rw [show D2M8K2.u8850 = KTree.node D2M8K2.u8846 (nat_lit 19427314) (nat_lit 4121195245) (nat_lit 0) D2M8K2.u8849 from rfl, allE_node, arows8846, irow8850, arows8849]
  all_goals rfl

theorem atot8850 : totK PD2M8K2 D2M8K2.u8850 = [504505778244, 2453672100864, 3182013369567, 959321011882, 45032108697, 0, 0, 0] := by
  rw [show D2M8K2.u8850 = KTree.node D2M8K2.u8846 (nat_lit 19427314) (nat_lit 4121195245) (nat_lit 0) D2M8K2.u8849 from rfl, totK_node, atot8846, atot8849]
  decide +kernel

theorem arows8857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8857 = true := by
  rw [show D2M8K2.u8857 = KTree.node D2M8K2.u8853 (nat_lit 19438203) (nat_lit 2023537775) (nat_lit 0) D2M8K2.u8856 from rfl, allE_node, arows8853, irow8857, arows8856]
  all_goals rfl

theorem atot8857 : totK PD2M8K2 D2M8K2.u8857 = [0, 1218667728202, 3530804416692, 2102155411402, 212641460071, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8857 = KTree.node D2M8K2.u8853 (nat_lit 19438203) (nat_lit 2023537775) (nat_lit 0) D2M8K2.u8856 from rfl, totK_node, atot8853, atot8856]
  decide +kernel

theorem arows8866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8866 = true := by
  rw [show D2M8K2.u8866 = KTree.node D2M8K2.u8862 (nat_lit 19454800) (nat_lit 2691294937) (nat_lit 0) D2M8K2.u8865 from rfl, allE_node, arows8862, irow8866, arows8865]
  all_goals rfl

theorem atot8866 : totK PD2M8K2 D2M8K2.u8866 = [534033002329, 2268948143611, 3149566571703, 1273878992418, 73601560104, 0, 0, 0] := by
  rw [show D2M8K2.u8866 = KTree.node D2M8K2.u8862 (nat_lit 19454800) (nat_lit 2691294937) (nat_lit 0) D2M8K2.u8865 from rfl, totK_node, atot8862, atot8865]
  decide +kernel

theorem arows8873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8873 = true := by
  rw [show D2M8K2.u8873 = KTree.node D2M8K2.u8869 (nat_lit 19461748) (nat_lit 1921937142) (nat_lit 0) D2M8K2.u8872 from rfl, allE_node, arows8869, irow8873, arows8872]
  all_goals rfl

theorem atot8873 : totK PD2M8K2 D2M8K2.u8873 = [860025049749, 2968832534992, 2803368324348, 607093332059, 23774305031, 0, 0, 0] := by
  rw [show D2M8K2.u8873 = KTree.node D2M8K2.u8869 (nat_lit 19461748) (nat_lit 1921937142) (nat_lit 0) D2M8K2.u8872 from rfl, totK_node, atot8869, atot8872]
  decide +kernel

theorem arows8881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8881 = true := by
  rw [show D2M8K2.u8881 = KTree.node D2M8K2.u8877 (nat_lit 19468380) (nat_lit 3033390448) (nat_lit 0) D2M8K2.u8880 from rfl, allE_node, arows8877, irow8881, arows8880]
  all_goals rfl

theorem atot8881 : totK PD2M8K2 D2M8K2.u8881 = [635013582905, 2676471563376, 3037082506247, 855699091075, 48917790063, 0, 0, 0] := by
  rw [show D2M8K2.u8881 = KTree.node D2M8K2.u8877 (nat_lit 19468380) (nat_lit 3033390448) (nat_lit 0) D2M8K2.u8880 from rfl, totK_node, atot8877, atot8880]
  decide +kernel

theorem arows8888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8888 = true := by
  rw [show D2M8K2.u8888 = KTree.node D2M8K2.u8884 (nat_lit 19478343) (nat_lit 3638030424) (nat_lit 0) D2M8K2.u8887 from rfl, allE_node, arows8884, irow8888, arows8887]
  all_goals rfl

theorem atot8888 : totK PD2M8K2 D2M8K2.u8888 = [0, 753409333754, 2775362355084, 2884628896992, 802569766685, 42081742489, 0, 0] := by
  rw [show D2M8K2.u8888 = KTree.node D2M8K2.u8884 (nat_lit 19478343) (nat_lit 3638030424) (nat_lit 0) D2M8K2.u8887 from rfl, totK_node, atot8884, atot8887]
  decide +kernel

theorem arows8898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8898 = true := by
  rw [show D2M8K2.u8898 = KTree.node D2M8K2.u8894 (nat_lit 19485547) (nat_lit 1650644940) (nat_lit 0) D2M8K2.u8897 from rfl, allE_node, arows8894, irow8898, arows8897]
  all_goals rfl

theorem atot8898 : totK PD2M8K2 D2M8K2.u8898 = [0, 912388940837, 3148923225433, 2717556814555, 440319531150, 6634014755, 0, 0] := by
  rw [show D2M8K2.u8898 = KTree.node D2M8K2.u8894 (nat_lit 19485547) (nat_lit 1650644940) (nat_lit 0) D2M8K2.u8897 from rfl, totK_node, atot8894, atot8897]
  decide +kernel

theorem arows8905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8905 = true := by
  rw [show D2M8K2.u8905 = KTree.node D2M8K2.u8901 (nat_lit 19534437) (nat_lit 1523717843) (nat_lit 0) D2M8K2.u8904 from rfl, allE_node, arows8901, irow8905, arows8904]
  all_goals rfl

theorem atot8905 : totK PD2M8K2 D2M8K2.u8905 = [721462360444, 2384818035608, 2524335914095, 1290589603360, 292190306712, 9302370699, 0, 0] := by
  rw [show D2M8K2.u8905 = KTree.node D2M8K2.u8901 (nat_lit 19534437) (nat_lit 1523717843) (nat_lit 0) D2M8K2.u8904 from rfl, totK_node, atot8901, atot8904]
  decide +kernel

theorem arows8913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8913 = true := by
  rw [show D2M8K2.u8913 = KTree.node D2M8K2.u8909 (nat_lit 19544222) (nat_lit 3823309974) (nat_lit 0) D2M8K2.u8912 from rfl, allE_node, arows8909, irow8913, arows8912]
  all_goals rfl

theorem atot8913 : totK PD2M8K2 D2M8K2.u8913 = [699667206146, 2661033284959, 2943788981033, 918951103712, 50594559506, 0, 0, 0] := by
  rw [show D2M8K2.u8913 = KTree.node D2M8K2.u8909 (nat_lit 19544222) (nat_lit 3823309974) (nat_lit 0) D2M8K2.u8912 from rfl, totK_node, atot8909, atot8912]
  decide +kernel

theorem arows8920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8920 = true := by
  rw [show D2M8K2.u8920 = KTree.node D2M8K2.u8916 (nat_lit 19551005) (nat_lit 2188214489) (nat_lit 0) D2M8K2.u8919 from rfl, allE_node, arows8916, irow8920, arows8919]
  all_goals rfl

theorem atot8920 : totK PD2M8K2 D2M8K2.u8920 = [708147398569, 2807239564231, 2983423178949, 705302016568, 26839988443, 0, 0, 0] := by
  rw [show D2M8K2.u8920 = KTree.node D2M8K2.u8916 (nat_lit 19551005) (nat_lit 2188214489) (nat_lit 0) D2M8K2.u8919 from rfl, totK_node, atot8916, atot8919]
  decide +kernel

theorem arows8929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8929 = true := by
  rw [show D2M8K2.u8929 = KTree.node D2M8K2.u8925 (nat_lit 19558216) (nat_lit 3619015797) (nat_lit 0) D2M8K2.u8928 from rfl, allE_node, arows8925, irow8929, arows8928]
  all_goals rfl

theorem atot8929 : totK PD2M8K2 D2M8K2.u8929 = [0, 1194121183699, 3538474729632, 2255147868092, 209105667371, 1239866073, 0, 0] := by
  rw [show D2M8K2.u8929 = KTree.node D2M8K2.u8925 (nat_lit 19558216) (nat_lit 3619015797) (nat_lit 0) D2M8K2.u8928 from rfl, totK_node, atot8925, atot8928]
  decide +kernel

theorem arows8936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8936 = true := by
  rw [show D2M8K2.u8936 = KTree.node D2M8K2.u8932 (nat_lit 19569247) (nat_lit 2395974345) (nat_lit 0) D2M8K2.u8935 from rfl, allE_node, arows8932, irow8936, arows8935]
  all_goals rfl

theorem atot8936 : totK PD2M8K2 D2M8K2.u8936 = [36508988125, 895183630035, 2983897438917, 2651149769616, 508442858876, 17826068843, 0, 0] := by
  rw [show D2M8K2.u8936 = KTree.node D2M8K2.u8932 (nat_lit 19569247) (nat_lit 2395974345) (nat_lit 0) D2M8K2.u8935 from rfl, totK_node, atot8932, atot8935]
  decide +kernel

theorem arows8944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8944 = true := by
  rw [show D2M8K2.u8944 = KTree.node D2M8K2.u8940 (nat_lit 19578770) (nat_lit 4106108950) (nat_lit 0) D2M8K2.u8943 from rfl, allE_node, arows8940, irow8944, arows8943]
  all_goals rfl

theorem atot8944 : totK PD2M8K2 D2M8K2.u8944 = [783567810476, 2872346276872, 2828594582568, 697757863360, 32158713694, 0, 0, 0] := by
  rw [show D2M8K2.u8944 = KTree.node D2M8K2.u8940 (nat_lit 19578770) (nat_lit 4106108950) (nat_lit 0) D2M8K2.u8943 from rfl, totK_node, atot8940, atot8943]
  decide +kernel

theorem arows8951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8951 = true := by
  rw [show D2M8K2.u8951 = KTree.node D2M8K2.u8947 (nat_lit 19585513) (nat_lit 1276281011) (nat_lit 0) D2M8K2.u8950 from rfl, allE_node, arows8947, irow8951, arows8950]
  all_goals rfl

theorem atot8951 : totK PD2M8K2 D2M8K2.u8951 = [835802349909, 2829671700514, 2752106084516, 710663225431, 32927661717, 0, 0, 0] := by
  rw [show D2M8K2.u8951 = KTree.node D2M8K2.u8947 (nat_lit 19585513) (nat_lit 1276281011) (nat_lit 0) D2M8K2.u8950 from rfl, totK_node, atot8947, atot8950]
  decide +kernel

theorem arows8963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8963 = true := by
  rw [show D2M8K2.u8963 = KTree.node D2M8K2.u8959 (nat_lit 19595684) (nat_lit 2777369328) (nat_lit 0) D2M8K2.u8962 from rfl, allE_node, arows8959, irow8963, arows8962]
  all_goals rfl

theorem atot8963 : totK PD2M8K2 D2M8K2.u8963 = [352152937815, 1959435209839, 3192602711095, 1491114031100, 142654664121, 1138244013, 0, 0] := by
  rw [show D2M8K2.u8963 = KTree.node D2M8K2.u8959 (nat_lit 19595684) (nat_lit 2777369328) (nat_lit 0) D2M8K2.u8962 from rfl, totK_node, atot8959, atot8962]
  decide +kernel

theorem arows8970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8970 = true := by
  rw [show D2M8K2.u8970 = KTree.node D2M8K2.u8966 (nat_lit 19606441) (nat_lit 969309433) (nat_lit 0) D2M8K2.u8969 from rfl, allE_node, arows8966, irow8970, arows8969]
  all_goals rfl

theorem atot8970 : totK PD2M8K2 D2M8K2.u8970 = [0, 1428030416504, 3735747973716, 1897613736902, 121237444019, 0, 0, 0] := by
  rw [show D2M8K2.u8970 = KTree.node D2M8K2.u8966 (nat_lit 19606441) (nat_lit 969309433) (nat_lit 0) D2M8K2.u8969 from rfl, totK_node, atot8966, atot8969]
  decide +kernel

theorem arows8978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8978 = true := by
  rw [show D2M8K2.u8978 = KTree.node D2M8K2.u8974 (nat_lit 19618560) (nat_lit 3719395728) (nat_lit 0) D2M8K2.u8977 from rfl, allE_node, arows8974, irow8978, arows8977]
  all_goals rfl

theorem atot8978 : totK PD2M8K2 D2M8K2.u8978 = [826775198619, 2666158106947, 2481763458196, 1027356647102, 194888120902, 4977114383, 0, 0] := by
  rw [show D2M8K2.u8978 = KTree.node D2M8K2.u8974 (nat_lit 19618560) (nat_lit 3719395728) (nat_lit 0) D2M8K2.u8977 from rfl, totK_node, atot8974, atot8977]
  decide +kernel

theorem arows8985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8985 = true := by
  rw [show D2M8K2.u8985 = KTree.node D2M8K2.u8981 (nat_lit 19625301) (nat_lit 1677357970) (nat_lit 0) D2M8K2.u8984 from rfl, allE_node, arows8981, irow8985, arows8984]
  all_goals rfl

theorem atot8985 : totK PD2M8K2 D2M8K2.u8985 = [753763151272, 2795780220018, 2947340773219, 752397029711, 24298984458, 0, 0, 0] := by
  rw [show D2M8K2.u8985 = KTree.node D2M8K2.u8981 (nat_lit 19625301) (nat_lit 1677357970) (nat_lit 0) D2M8K2.u8984 from rfl, totK_node, atot8981, atot8984]
  decide +kernel

theorem arows8994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8994 = true := by
  rw [show D2M8K2.u8994 = KTree.node D2M8K2.u8990 (nat_lit 19635678) (nat_lit 3871512974) (nat_lit 0) D2M8K2.u8993 from rfl, allE_node, arows8990, irow8994, arows8993]
  all_goals rfl

theorem atot8994 : totK PD2M8K2 D2M8K2.u8994 = [441860355822, 2147516103068, 3185181321330, 1296823396487, 108008008154, 1310285577, 0, 0] := by
  rw [show D2M8K2.u8994 = KTree.node D2M8K2.u8990 (nat_lit 19635678) (nat_lit 3871512974) (nat_lit 0) D2M8K2.u8993 from rfl, totK_node, atot8990, atot8993]
  decide +kernel

theorem arows9001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9001 = true := by
  rw [show D2M8K2.u9001 = KTree.node D2M8K2.u8997 (nat_lit 19644364) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u9000 from rfl, allE_node, arows8997, irow9001, arows9000]
  all_goals rfl

theorem atot9001 : totK PD2M8K2 D2M8K2.u9001 = [0, 1064559930406, 3300307030630, 2530490411619, 329594067492, 4879840392, 0, 0] := by
  rw [show D2M8K2.u9001 = KTree.node D2M8K2.u8997 (nat_lit 19644364) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u9000 from rfl, totK_node, atot8997, atot9000]
  decide +kernel

theorem arows9009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9009 = true := by
  rw [show D2M8K2.u9009 = KTree.node D2M8K2.u9005 (nat_lit 19655364) (nat_lit 2951353805) (nat_lit 0) D2M8K2.u9008 from rfl, allE_node, arows9005, irow9009, arows9008]
  all_goals rfl

theorem atot9009 : totK PD2M8K2 D2M8K2.u9009 = [0, 801825762770, 2934939043805, 2754357178135, 615470265584, 26682572712, 0, 0] := by
  rw [show D2M8K2.u9009 = KTree.node D2M8K2.u9005 (nat_lit 19655364) (nat_lit 2951353805) (nat_lit 0) D2M8K2.u9008 from rfl, totK_node, atot9005, atot9008]
  decide +kernel

theorem arows9016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9016 = true := by
  rw [show D2M8K2.u9016 = KTree.node D2M8K2.u9012 (nat_lit 19666218) (nat_lit 3599043647) (nat_lit 0) D2M8K2.u9015 from rfl, allE_node, arows9012, irow9016, arows9015]
  all_goals rfl

theorem atot9016 : totK PD2M8K2 D2M8K2.u9016 = [0, 920281723369, 3198529162771, 2677378331472, 366479190611, 3731543444, 0, 0] := by
  rw [show D2M8K2.u9016 = KTree.node D2M8K2.u9012 (nat_lit 19666218) (nat_lit 3599043647) (nat_lit 0) D2M8K2.u9015 from rfl, totK_node, atot9012, atot9015]
  decide +kernel

theorem arows9026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9026 = true := by
  rw [show D2M8K2.u9026 = KTree.node D2M8K2.u9022 (nat_lit 19673410) (nat_lit 3919507834) (nat_lit 0) D2M8K2.u9025 from rfl, allE_node, arows9022, irow9026, arows9025]
  all_goals rfl

theorem atot9026 : totK PD2M8K2 D2M8K2.u9026 = [0, 821375927406, 2920622544630, 2806664288393, 569865149963, 18178349234, 0, 0] := by
  rw [show D2M8K2.u9026 = KTree.node D2M8K2.u9022 (nat_lit 19673410) (nat_lit 3919507834) (nat_lit 0) D2M8K2.u9025 from rfl, totK_node, atot9022, atot9025]
  decide +kernel

theorem arows9033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9033 = true := by
  rw [show D2M8K2.u9033 = KTree.node D2M8K2.u9029 (nat_lit 19680386) (nat_lit 1334764274) (nat_lit 0) D2M8K2.u9032 from rfl, allE_node, arows9029, irow9033, arows9032]
  all_goals rfl

theorem atot9033 : totK PD2M8K2 D2M8K2.u9033 = [0, 0, 1406628085055, 3644639023494, 1782776489423, 149480928834, 1310517177, 0] := by
  rw [show D2M8K2.u9033 = KTree.node D2M8K2.u9029 (nat_lit 19680386) (nat_lit 1334764274) (nat_lit 0) D2M8K2.u9032 from rfl, totK_node, atot9029, atot9032]
  decide +kernel

theorem arows9041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9041 = true := by
  rw [show D2M8K2.u9041 = KTree.node D2M8K2.u9037 (nat_lit 19696826) (nat_lit 3878748063) (nat_lit 0) D2M8K2.u9040 from rfl, allE_node, arows9037, irow9041, arows9040]
  all_goals rfl

theorem atot9041 : totK PD2M8K2 D2M8K2.u9041 = [0, 443852820150, 2220485696585, 3265413299462, 1183873744004, 66901944603, 0, 0] := by
  rw [show D2M8K2.u9041 = KTree.node D2M8K2.u9037 (nat_lit 19696826) (nat_lit 3878748063) (nat_lit 0) D2M8K2.u9040 from rfl, totK_node, atot9037, atot9040]
  decide +kernel

theorem arows9048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9048 = true := by
  rw [show D2M8K2.u9048 = KTree.node D2M8K2.u9044 (nat_lit 19709034) (nat_lit 3476878735) (nat_lit 0) D2M8K2.u9047 from rfl, allE_node, arows9044, irow9048, arows9047]
  all_goals rfl

theorem atot9048 : totK PD2M8K2 D2M8K2.u9048 = [0, 755045632360, 2781234808055, 2934254397436, 773466919864, 25863538377, 0, 0] := by
  rw [show D2M8K2.u9048 = KTree.node D2M8K2.u9044 (nat_lit 19709034) (nat_lit 3476878735) (nat_lit 0) D2M8K2.u9047 from rfl, totK_node, atot9044, atot9047]
  decide +kernel

theorem arows9057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9057 = true := by
  rw [show D2M8K2.u9057 = KTree.node D2M8K2.u9053 (nat_lit 19715911) (nat_lit 2315560745) (nat_lit 0) D2M8K2.u9056 from rfl, allE_node, arows9053, irow9057, arows9056]
  all_goals rfl

theorem atot9057 : totK PD2M8K2 D2M8K2.u9057 = [0, 827646225612, 3012547156386, 2837826852973, 545525209018, 12370078298, 0, 0] := by
  rw [show D2M8K2.u9057 = KTree.node D2M8K2.u9053 (nat_lit 19715911) (nat_lit 2315560745) (nat_lit 0) D2M8K2.u9056 from rfl, totK_node, atot9053, atot9056]
  decide +kernel

theorem arows9064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9064 = true := by
  rw [show D2M8K2.u9064 = KTree.node D2M8K2.u9060 (nat_lit 19785077) (nat_lit 2223915799) (nat_lit 0) D2M8K2.u9063 from rfl, allE_node, arows9060, irow9064, arows9063]
  all_goals rfl

theorem atot9064 : totK PD2M8K2 D2M8K2.u9064 = [0, 841184958943, 2920803328301, 2749116830856, 661116229117, 36251906512, 0, 0] := by
  rw [show D2M8K2.u9064 = KTree.node D2M8K2.u9060 (nat_lit 19785077) (nat_lit 2223915799) (nat_lit 0) D2M8K2.u9063 from rfl, totK_node, atot9060, atot9063]
  decide +kernel

theorem arows9072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9072 = true := by
  rw [show D2M8K2.u9072 = KTree.node D2M8K2.u9068 (nat_lit 19794598) (nat_lit 3653355323) (nat_lit 0) D2M8K2.u9071 from rfl, allE_node, arows9068, irow9072, arows9071]
  all_goals rfl

theorem atot9072 : totK PD2M8K2 D2M8K2.u9072 = [0, 864081072768, 2907005053936, 2730330812479, 676586579086, 24925710081, 0, 0] := by
  rw [show D2M8K2.u9072 = KTree.node D2M8K2.u9068 (nat_lit 19794598) (nat_lit 3653355323) (nat_lit 0) D2M8K2.u9071 from rfl, totK_node, atot9068, atot9071]
  decide +kernel

theorem arows9079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9079 = true := by
  rw [show D2M8K2.u9079 = KTree.node D2M8K2.u9075 (nat_lit 19801423) (nat_lit 1792094332) (nat_lit 0) D2M8K2.u9078 from rfl, allE_node, arows9075, irow9079, arows9078]
  all_goals rfl

theorem atot9079 : totK PD2M8K2 D2M8K2.u9079 = [0, 423018951437, 2246898835996, 3307142914572, 1082970261885, 54569901267, 0, 0] := by
  rw [show D2M8K2.u9079 = KTree.node D2M8K2.u9075 (nat_lit 19801423) (nat_lit 1792094332) (nat_lit 0) D2M8K2.u9078 from rfl, totK_node, atot9075, atot9078]
  decide +kernel

theorem arows9090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9090 = true := by
  rw [show D2M8K2.u9090 = KTree.node D2M8K2.u9086 (nat_lit 19813806) (nat_lit 3845978438) (nat_lit 0) D2M8K2.u9089 from rfl, allE_node, arows9086, irow9090, arows9089]
  all_goals rfl

theorem atot9090 : totK PD2M8K2 D2M8K2.u9090 = [0, 0, 1028671625774, 3196423930076, 2421164227968, 430703959979, 14322947163, 0] := by
  rw [show D2M8K2.u9090 = KTree.node D2M8K2.u9086 (nat_lit 19813806) (nat_lit 3845978438) (nat_lit 0) D2M8K2.u9089 from rfl, totK_node, atot9086, atot9089]
  decide +kernel

theorem arows9097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9097 = true := by
  rw [show D2M8K2.u9097 = KTree.node D2M8K2.u9093 (nat_lit 19821024) (nat_lit 3691789053) (nat_lit 0) D2M8K2.u9096 from rfl, allE_node, arows9093, irow9097, arows9096]
  all_goals rfl

theorem atot9097 : totK PD2M8K2 D2M8K2.u9097 = [0, 405454907483, 1912634640885, 2949626318399, 1537688274760, 198969682601, 4630915822, 0] := by
  rw [show D2M8K2.u9097 = KTree.node D2M8K2.u9093 (nat_lit 19821024) (nat_lit 3691789053) (nat_lit 0) D2M8K2.u9096 from rfl, totK_node, atot9093, atot9096]
  decide +kernel

theorem arows9105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9105 = true := by
  rw [show D2M8K2.u9105 = KTree.node D2M8K2.u9101 (nat_lit 19829904) (nat_lit 2859338497) (nat_lit 0) D2M8K2.u9104 from rfl, allE_node, arows9101, irow9105, arows9104]
  all_goals rfl

theorem atot9105 : totK PD2M8K2 D2M8K2.u9105 = [0, 824679553080, 2920576079204, 2844407108621, 614577113862, 19599137318, 0, 0] := by
  rw [show D2M8K2.u9105 = KTree.node D2M8K2.u9101 (nat_lit 19829904) (nat_lit 2859338497) (nat_lit 0) D2M8K2.u9104 from rfl, totK_node, atot9101, atot9104]
  decide +kernel

theorem arows9112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9112 = true := by
  rw [show D2M8K2.u9112 = KTree.node D2M8K2.u9108 (nat_lit 19837458) (nat_lit 3391139419) (nat_lit 0) D2M8K2.u9111 from rfl, allE_node, arows9108, irow9112, arows9111]
  all_goals rfl

theorem atot9112 : totK PD2M8K2 D2M8K2.u9112 = [0, 778860860136, 2959039228317, 2875528637436, 586794834047, 18231200220, 0, 0] := by
  rw [show D2M8K2.u9112 = KTree.node D2M8K2.u9108 (nat_lit 19837458) (nat_lit 3391139419) (nat_lit 0) D2M8K2.u9111 from rfl, totK_node, atot9108, atot9111]
  decide +kernel

theorem arows9121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9121 = true := by
  rw [show D2M8K2.u9121 = KTree.node D2M8K2.u9117 (nat_lit 19848701) (nat_lit 1814707960) (nat_lit 0) D2M8K2.u9120 from rfl, allE_node, arows9117, irow9121, arows9120]
  all_goals rfl

theorem atot9121 : totK PD2M8K2 D2M8K2.u9121 = [0, 0, 1422674771770, 3641913893773, 1787669601049, 132006118328, 1138244013, 0] := by
  rw [show D2M8K2.u9121 = KTree.node D2M8K2.u9117 (nat_lit 19848701) (nat_lit 1814707960) (nat_lit 0) D2M8K2.u9120 from rfl, totK_node, atot9117, atot9120]
  decide +kernel

theorem arows9128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9128 = true := by
  rw [show D2M8K2.u9128 = KTree.node D2M8K2.u9124 (nat_lit 19860894) (nat_lit 3896957689) (nat_lit 0) D2M8K2.u9127 from rfl, allE_node, arows9124, irow9128, arows9127]
  all_goals rfl

theorem atot9128 : totK PD2M8K2 D2M8K2.u9128 = [0, 406958004779, 1955825827904, 2987383818829, 1456749346724, 189990431871, 4914284239, 0] := by
  rw [show D2M8K2.u9128 = KTree.node D2M8K2.u9124 (nat_lit 19860894) (nat_lit 3896957689) (nat_lit 0) D2M8K2.u9127 from rfl, totK_node, atot9124, atot9127]
  decide +kernel

theorem arows9136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9136 = true := by
  rw [show D2M8K2.u9136 = KTree.node D2M8K2.u9132 (nat_lit 19871527) (nat_lit 2329157819) (nat_lit 0) D2M8K2.u9135 from rfl, allE_node, arows9132, irow9136, arows9135]
  all_goals rfl

theorem atot9136 : totK PD2M8K2 D2M8K2.u9136 = [0, 829223753013, 2792392188338, 2815765232638, 788571921234, 37977415854, 0, 0] := by
  rw [show D2M8K2.u9136 = KTree.node D2M8K2.u9132 (nat_lit 19871527) (nat_lit 2329157819) (nat_lit 0) D2M8K2.u9135 from rfl, totK_node, atot9132, atot9135]
  decide +kernel

theorem arows9143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9143 = true := by
  rw [show D2M8K2.u9143 = KTree.node D2M8K2.u9139 (nat_lit 19882416) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u9142 from rfl, allE_node, arows9139, irow9143, arows9142]
  all_goals rfl

theorem atot9143 : totK PD2M8K2 D2M8K2.u9143 = [0, 783019159570, 2894046521007, 2866945926066, 661558648543, 21827774825, 0, 0] := by
  rw [show D2M8K2.u9143 = KTree.node D2M8K2.u9139 (nat_lit 19882416) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u9142 from rfl, totK_node, atot9139, atot9142]
  decide +kernel

theorem arows9153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9153 = true := by
  rw [show D2M8K2.u9153 = KTree.node D2M8K2.u9149 (nat_lit 19909531) (nat_lit 2104014189) (nat_lit 0) D2M8K2.u9152 from rfl, allE_node, arows9149, irow9153, arows9152]
  all_goals rfl

theorem atot9153 : totK PD2M8K2 D2M8K2.u9153 = [812752260945, 2833165333972, 2625244554203, 704886622757, 147117124783, 13338039113, 0, 0] := by
  rw [show D2M8K2.u9153 = KTree.node D2M8K2.u9149 (nat_lit 19909531) (nat_lit 2104014189) (nat_lit 0) D2M8K2.u9152 from rfl, totK_node, atot9149, atot9152]
  decide +kernel

theorem arows9160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9160 = true := by
  rw [show D2M8K2.u9160 = KTree.node D2M8K2.u9156 (nat_lit 19920102) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u9159 from rfl, allE_node, arows9156, irow9160, arows9159]
  all_goals rfl

theorem atot9160 : totK PD2M8K2 D2M8K2.u9160 = [834705093380, 2999005650181, 2804903694757, 540739389757, 15416603213, 0, 0, 0] := by
  rw [show D2M8K2.u9160 = KTree.node D2M8K2.u9156 (nat_lit 19920102) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u9159 from rfl, totK_node, atot9156, atot9159]
  decide +kernel

theorem arows9168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9168 = true := by
  rw [show D2M8K2.u9168 = KTree.node D2M8K2.u9164 (nat_lit 19927488) (nat_lit 3599503489) (nat_lit 0) D2M8K2.u9167 from rfl, allE_node, arows9164, irow9168, arows9167]
  all_goals rfl

theorem atot9168 : totK PD2M8K2 D2M8K2.u9168 = [326462839732, 1725615959777, 3108959556785, 1701019416758, 190718459317, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9168 = KTree.node D2M8K2.u9164 (nat_lit 19927488) (nat_lit 3599503489) (nat_lit 0) D2M8K2.u9167 from rfl, totK_node, atot9164, atot9167]
  decide +kernel

theorem arows9175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9175 = true := by
  rw [show D2M8K2.u9175 = KTree.node D2M8K2.u9171 (nat_lit 19941272) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u9174 from rfl, allE_node, arows9171, irow9175, arows9174]
  all_goals rfl

theorem atot9175 : totK PD2M8K2 D2M8K2.u9175 = [94305354095, 1552442435359, 3654933262065, 1744491683566, 98029138226, 0, 0, 0] := by
  rw [show D2M8K2.u9175 = KTree.node D2M8K2.u9171 (nat_lit 19941272) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u9174 from rfl, totK_node, atot9171, atot9174]
  decide +kernel

theorem arows9184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9184 = true := by
  rw [show D2M8K2.u9184 = KTree.node D2M8K2.u9180 (nat_lit 19954571) (nat_lit 1212497212) (nat_lit 0) D2M8K2.u9183 from rfl, allE_node, arows9180, irow9184, arows9183]
  all_goals rfl

theorem atot9184 : totK PD2M8K2 D2M8K2.u9184 = [731827149920, 2723420793054, 2895958860479, 855470377415, 47190322183, 0, 0, 0] := by
  rw [show D2M8K2.u9184 = KTree.node D2M8K2.u9180 (nat_lit 19954571) (nat_lit 1212497212) (nat_lit 0) D2M8K2.u9183 from rfl, totK_node, atot9180, atot9183]
  decide +kernel

theorem arows9191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9191 = true := by
  rw [show D2M8K2.u9191 = KTree.node D2M8K2.u9187 (nat_lit 19961384) (nat_lit 3943022322) (nat_lit 0) D2M8K2.u9190 from rfl, allE_node, arows9187, irow9191, arows9190]
  all_goals rfl

theorem atot9191 : totK PD2M8K2 D2M8K2.u9191 = [838935399358, 2998303202402, 2823754785840, 573059550682, 17789768395, 0, 0, 0] := by
  rw [show D2M8K2.u9191 = KTree.node D2M8K2.u9187 (nat_lit 19961384) (nat_lit 3943022322) (nat_lit 0) D2M8K2.u9190 from rfl, totK_node, atot9187, atot9190]
  decide +kernel

theorem arows9199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9199 = true := by
  rw [show D2M8K2.u9199 = KTree.node D2M8K2.u9195 (nat_lit 19972603) (nat_lit 2213486359) (nat_lit 0) D2M8K2.u9198 from rfl, allE_node, arows9195, irow9199, arows9198]
  all_goals rfl

theorem atot9199 : totK PD2M8K2 D2M8K2.u9199 = [333067881029, 1689363019933, 2931512133432, 1874037294354, 439098534199, 29044448997, 0, 0] := by
  rw [show D2M8K2.u9199 = KTree.node D2M8K2.u9195 (nat_lit 19972603) (nat_lit 2213486359) (nat_lit 0) D2M8K2.u9198 from rfl, totK_node, atot9195, atot9198]
  decide +kernel

theorem arows9206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9206 = true := by
  rw [show D2M8K2.u9206 = KTree.node D2M8K2.u9202 (nat_lit 19978800) (nat_lit 3111052739) (nat_lit 0) D2M8K2.u9205 from rfl, allE_node, arows9202, irow9206, arows9205]
  all_goals rfl

theorem atot9206 : totK PD2M8K2 D2M8K2.u9206 = [0, 798322859674, 2891571802311, 2857579833250, 641977923805, 18256166177, 0, 0] := by
  rw [show D2M8K2.u9206 = KTree.node D2M8K2.u9202 (nat_lit 19978800) (nat_lit 3111052739) (nat_lit 0) D2M8K2.u9205 from rfl, totK_node, atot9202, atot9205]
  decide +kernel

theorem arows9220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9220 = true := by
  rw [show D2M8K2.u9220 = KTree.node D2M8K2.u9216 (nat_lit 19986422) (nat_lit 3990225091) (nat_lit 0) D2M8K2.u9219 from rfl, allE_node, arows9216, irow9220, arows9219]
  all_goals rfl

theorem atot9220 : totK PD2M8K2 D2M8K2.u9220 = [176055752117, 1144653495004, 2835731566574, 2584441117838, 503047765931, 10717512769, 0, 0] := by
  rw [show D2M8K2.u9220 = KTree.node D2M8K2.u9216 (nat_lit 19986422) (nat_lit 3990225091) (nat_lit 0) D2M8K2.u9219 from rfl, totK_node, atot9216, atot9219]
  decide +kernel

theorem arows9227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9227 = true := by
  rw [show D2M8K2.u9227 = KTree.node D2M8K2.u9223 (nat_lit 19993950) (nat_lit 3847597743) (nat_lit 0) D2M8K2.u9226 from rfl, allE_node, arows9223, irow9227, arows9226]
  all_goals rfl

theorem atot9227 : totK PD2M8K2 D2M8K2.u9227 = [798922587941, 2821489442251, 2796485053321, 767739217514, 38933689765, 0, 0, 0] := by
  rw [show D2M8K2.u9227 = KTree.node D2M8K2.u9223 (nat_lit 19993950) (nat_lit 3847597743) (nat_lit 0) D2M8K2.u9226 from rfl, totK_node, atot9223, atot9226]
  decide +kernel

theorem arows9235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9235 = true := by
  rw [show D2M8K2.u9235 = KTree.node D2M8K2.u9231 (nat_lit 20003680) (nat_lit 3741771442) (nat_lit 0) D2M8K2.u9234 from rfl, allE_node, arows9231, irow9235, arows9234]
  all_goals rfl

theorem atot9235 : totK PD2M8K2 D2M8K2.u9235 = [676680577296, 2788283027464, 3043870179166, 675998422573, 19400062646, 0, 0, 0] := by
  rw [show D2M8K2.u9235 = KTree.node D2M8K2.u9231 (nat_lit 20003680) (nat_lit 3741771442) (nat_lit 0) D2M8K2.u9234 from rfl, totK_node, atot9231, atot9234]
  decide +kernel

theorem arows9242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9242 = true := by
  rw [show D2M8K2.u9242 = KTree.node D2M8K2.u9238 (nat_lit 20014694) (nat_lit 3979250802) (nat_lit 0) D2M8K2.u9241 from rfl, allE_node, arows9238, irow9242, arows9241]
  all_goals rfl

theorem atot9242 : totK PD2M8K2 D2M8K2.u9242 = [0, 1081732808022, 3377326697677, 2360660398434, 278237173741, 2369401571, 0, 0] := by
  rw [show D2M8K2.u9242 = KTree.node D2M8K2.u9238 (nat_lit 20014694) (nat_lit 3979250802) (nat_lit 0) D2M8K2.u9241 from rfl, totK_node, atot9238, atot9241]
  decide +kernel

theorem arows9251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9251 = true := by
  rw [show D2M8K2.u9251 = KTree.node D2M8K2.u9247 (nat_lit 20026379) (nat_lit 2245933952) (nat_lit 0) D2M8K2.u9250 from rfl, allE_node, arows9247, irow9251, arows9250]
  all_goals rfl

theorem atot9251 : totK PD2M8K2 D2M8K2.u9251 = [407284249840, 1710493272662, 2688921734931, 1839713657822, 372321003861, 16427657237, 0, 0] := by
  rw [show D2M8K2.u9251 = KTree.node D2M8K2.u9247 (nat_lit 20026379) (nat_lit 2245933952) (nat_lit 0) D2M8K2.u9250 from rfl, totK_node, atot9247, atot9250]
  decide +kernel

theorem arows9258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9258 = true := by
  rw [show D2M8K2.u9258 = KTree.node D2M8K2.u9254 (nat_lit 20037154) (nat_lit 4117617877) (nat_lit 0) D2M8K2.u9257 from rfl, allE_node, arows9254, irow9258, arows9257]
  all_goals rfl

theorem atot9258 : totK PD2M8K2 D2M8K2.u9258 = [859752578246, 2895204200366, 2767981456851, 750495388065, 38610378334, 0, 0, 0] := by
  rw [show D2M8K2.u9258 = KTree.node D2M8K2.u9254 (nat_lit 20037154) (nat_lit 4117617877) (nat_lit 0) D2M8K2.u9257 from rfl, totK_node, atot9254, atot9257]
  decide +kernel

theorem arows9266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9266 = true := by
  rw [show D2M8K2.u9266 = KTree.node D2M8K2.u9262 (nat_lit 20046681) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u9265 from rfl, allE_node, arows9262, irow9266, arows9265]
  all_goals rfl

theorem atot9266 : totK PD2M8K2 D2M8K2.u9266 = [769828837225, 2916179862446, 2941967744015, 614618337516, 18301866131, 0, 0, 0] := by
  rw [show D2M8K2.u9266 = KTree.node D2M8K2.u9262 (nat_lit 20046681) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u9265 from rfl, totK_node, atot9262, atot9265]
  decide +kernel

theorem arows9273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9273 = true := by
  rw [show D2M8K2.u9273 = KTree.node D2M8K2.u9269 (nat_lit 20054645) (nat_lit 2319331805) (nat_lit 0) D2M8K2.u9272 from rfl, allE_node, arows9269, irow9273, arows9272]
  all_goals rfl

theorem atot9273 : totK PD2M8K2 D2M8K2.u9273 = [0, 1231123686553, 3536214651886, 2195745436055, 210054173062, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9273 = KTree.node D2M8K2.u9269 (nat_lit 20054645) (nat_lit 2319331805) (nat_lit 0) D2M8K2.u9272 from rfl, totK_node, atot9269, atot9272]
  decide +kernel

theorem arows9283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9283 = true := by
  rw [show D2M8K2.u9283 = KTree.node D2M8K2.u9279 (nat_lit 20066257) (nat_lit 1507513746) (nat_lit 0) D2M8K2.u9282 from rfl, allE_node, arows9279, irow9283, arows9282]
  all_goals rfl

theorem atot9283 : totK PD2M8K2 D2M8K2.u9283 = [0, 848621406150, 3033633504308, 2683618940146, 508375910285, 17826068843, 0, 0] := by
  rw [show D2M8K2.u9283 = KTree.node D2M8K2.u9279 (nat_lit 20066257) (nat_lit 1507513746) (nat_lit 0) D2M8K2.u9282 from rfl, totK_node, atot9279, atot9282]
  decide +kernel

theorem arows9290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9290 = true := by
  rw [show D2M8K2.u9290 = KTree.node D2M8K2.u9286 (nat_lit 20075438) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u9289 from rfl, allE_node, arows9286, irow9290, arows9289]
  all_goals rfl

theorem atot9290 : totK PD2M8K2 D2M8K2.u9290 = [835159654126, 2899623369551, 2726263006814, 697882845166, 43046734388, 0, 0, 0] := by
  rw [show D2M8K2.u9290 = KTree.node D2M8K2.u9286 (nat_lit 20075438) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u9289 from rfl, totK_node, atot9286, atot9289]
  decide +kernel

theorem arows9298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9298 = true := by
  rw [show D2M8K2.u9298 = KTree.node D2M8K2.u9294 (nat_lit 20081764) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u9297 from rfl, allE_node, arows9294, irow9298, arows9297]
  all_goals rfl

theorem atot9298 : totK PD2M8K2 D2M8K2.u9298 = [822867729070, 2867912176996, 2780298024146, 674819299606, 23425771837, 0, 0, 0] := by
  rw [show D2M8K2.u9298 = KTree.node D2M8K2.u9294 (nat_lit 20081764) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u9297 from rfl, totK_node, atot9294, atot9297]
  decide +kernel

theorem arows9305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9305 = true := by
  rw [show D2M8K2.u9305 = KTree.node D2M8K2.u9301 (nat_lit 20088361) (nat_lit 1202701148) (nat_lit 0) D2M8K2.u9304 from rfl, allE_node, arows9301, irow9305, arows9304]
  all_goals rfl

theorem atot9305 : totK PD2M8K2 D2M8K2.u9305 = [444328224940, 2195177592182, 3164561172502, 1229063971663, 104216144473, 1138244013, 0, 0] := by
  rw [show D2M8K2.u9305 = KTree.node D2M8K2.u9301 (nat_lit 20088361) (nat_lit 1202701148) (nat_lit 0) D2M8K2.u9304 from rfl, totK_node, atot9301, atot9304]
  decide +kernel

theorem arows9314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9314 = true := by
  rw [show D2M8K2.u9314 = KTree.node D2M8K2.u9310 (nat_lit 20100781) (nat_lit 1117684301) (nat_lit 0) D2M8K2.u9313 from rfl, allE_node, arows9310, irow9314, arows9313]
  all_goals rfl

theorem atot9314 : totK PD2M8K2 D2M8K2.u9314 = [0, 1415828868362, 3728340790691, 1912692892720, 125876905346, 0, 0, 0] := by
  rw [show D2M8K2.u9314 = KTree.node D2M8K2.u9310 (nat_lit 20100781) (nat_lit 1117684301) (nat_lit 0) D2M8K2.u9313 from rfl, totK_node, atot9310, atot9313]
  decide +kernel

theorem arows9321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9321 = true := by
  rw [show D2M8K2.u9321 = KTree.node D2M8K2.u9317 (nat_lit 20156119) (nat_lit 1219313662) (nat_lit 0) D2M8K2.u9320 from rfl, allE_node, arows9317, irow9321, arows9320]
  all_goals rfl

theorem atot9321 : totK PD2M8K2 D2M8K2.u9321 = [0, 893554975076, 3159141502350, 2657234588146, 408573623260, 6346264815, 0, 0] := by
  rw [show D2M8K2.u9321 = KTree.node D2M8K2.u9317 (nat_lit 20156119) (nat_lit 1219313662) (nat_lit 0) D2M8K2.u9320 from rfl, totK_node, atot9317, atot9320]
  decide +kernel

theorem arows9329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9329 = true := by
  rw [show D2M8K2.u9329 = KTree.node D2M8K2.u9325 (nat_lit 20166781) (nat_lit 1184706117) (nat_lit 0) D2M8K2.u9328 from rfl, allE_node, arows9325, irow9329, arows9328]
  all_goals rfl

theorem atot9329 : totK PD2M8K2 D2M8K2.u9329 = [0, 839583828078, 2894639460464, 2752898657205, 594472653980, 26167767196, 0, 0] := by
  rw [show D2M8K2.u9329 = KTree.node D2M8K2.u9325 (nat_lit 20166781) (nat_lit 1184706117) (nat_lit 0) D2M8K2.u9328 from rfl, totK_node, atot9325, atot9328]
  decide +kernel

theorem arows9336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9336 = true := by
  rw [show D2M8K2.u9336 = KTree.node D2M8K2.u9332 (nat_lit 20173807) (nat_lit 2284194665) (nat_lit 0) D2M8K2.u9335 from rfl, allE_node, arows9332, irow9336, arows9335]
  all_goals rfl

theorem atot9336 : totK PD2M8K2 D2M8K2.u9336 = [0, 502686893938, 2521096205451, 3186357159644, 844031315336, 35260582703, 0, 0] := by
  rw [show D2M8K2.u9336 = KTree.node D2M8K2.u9332 (nat_lit 20173807) (nat_lit 2284194665) (nat_lit 0) D2M8K2.u9335 from rfl, totK_node, atot9332, atot9335]
  decide +kernel

theorem arows9347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9347 = true := by
  rw [show D2M8K2.u9347 = KTree.node D2M8K2.u9343 (nat_lit 20187690) (nat_lit 3795580057) (nat_lit 0) D2M8K2.u9346 from rfl, allE_node, arows9343, irow9347, arows9346]
  all_goals rfl

theorem atot9347 : totK PD2M8K2 D2M8K2.u9347 = [0, 41386975132, 1580811831343, 3643222905732, 1611967053268, 131107604885, 1209030869, 0] := by
  rw [show D2M8K2.u9347 = KTree.node D2M8K2.u9343 (nat_lit 20187690) (nat_lit 3795580057) (nat_lit 0) D2M8K2.u9346 from rfl, totK_node, atot9343, atot9346]
  decide +kernel

theorem arows9354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9354 = true := by
  rw [show D2M8K2.u9354 = KTree.node D2M8K2.u9350 (nat_lit 20203292) (nat_lit 3386744858) (nat_lit 0) D2M8K2.u9353 from rfl, allE_node, arows9350, irow9354, arows9353]
  all_goals rfl

theorem atot9354 : totK PD2M8K2 D2M8K2.u9354 = [0, 779848501026, 2811032579041, 2837284745324, 798955007781, 45916062397, 0, 0] := by
  rw [show D2M8K2.u9354 = KTree.node D2M8K2.u9350 (nat_lit 20203292) (nat_lit 3386744858) (nat_lit 0) D2M8K2.u9353 from rfl, totK_node, atot9350, atot9353]
  decide +kernel

theorem arows9362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9362 = true := by
  rw [show D2M8K2.u9362 = KTree.node D2M8K2.u9358 (nat_lit 20210334) (nat_lit 3962805460) (nat_lit 0) D2M8K2.u9361 from rfl, allE_node, arows9358, irow9362, arows9361]
  all_goals rfl

theorem atot9362 : totK PD2M8K2 D2M8K2.u9362 = [0, 837091902107, 3044322356797, 2821834062180, 531847333704, 16563597585, 0, 0] := by
  rw [show D2M8K2.u9362 = KTree.node D2M8K2.u9358 (nat_lit 20210334) (nat_lit 3962805460) (nat_lit 0) D2M8K2.u9361 from rfl, totK_node, atot9358, atot9361]
  decide +kernel

theorem arows9369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9369 = true := by
  rw [show D2M8K2.u9369 = KTree.node D2M8K2.u9365 (nat_lit 20238947) (nat_lit 2257984342) (nat_lit 0) D2M8K2.u9368 from rfl, allE_node, arows9365, irow9369, arows9368]
  all_goals rfl

theorem atot9369 : totK PD2M8K2 D2M8K2.u9369 = [0, 907090065995, 3030511918487, 2734126325499, 535086523024, 13854043027, 0, 0] := by
  rw [show D2M8K2.u9369 = KTree.node D2M8K2.u9365 (nat_lit 20238947) (nat_lit 2257984342) (nat_lit 0) D2M8K2.u9368 from rfl, totK_node, atot9365, atot9368]
  decide +kernel

theorem arows9378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9378 = true := by
  rw [show D2M8K2.u9378 = KTree.node D2M8K2.u9374 (nat_lit 20245810) (nat_lit 4121252693) (nat_lit 0) D2M8K2.u9377 from rfl, allE_node, arows9374, irow9378, arows9377]
  all_goals rfl

theorem atot9378 : totK PD2M8K2 D2M8K2.u9378 = [0, 821796147686, 2881026160958, 2811883099953, 702871352160, 28063716506, 0, 0] := by
  rw [show D2M8K2.u9378 = KTree.node D2M8K2.u9374 (nat_lit 20245810) (nat_lit 4121252693) (nat_lit 0) D2M8K2.u9377 from rfl, totK_node, atot9374, atot9377]
  decide +kernel

theorem arows9385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9385 = true := by
  rw [show D2M8K2.u9385 = KTree.node D2M8K2.u9381 (nat_lit 20280679) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u9384 from rfl, allE_node, arows9381, irow9385, arows9384]
  all_goals rfl

theorem atot9385 : totK PD2M8K2 D2M8K2.u9385 = [0, 907685024252, 3131676824198, 2736137049461, 410893974310, 6291032136, 0, 0] := by
  rw [show D2M8K2.u9385 = KTree.node D2M8K2.u9381 (nat_lit 20280679) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u9384 from rfl, totK_node, atot9381, atot9384]
  decide +kernel

theorem arows9393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9393 = true := by
  rw [show D2M8K2.u9393 = KTree.node D2M8K2.u9389 (nat_lit 20291112) (nat_lit 3582658539) (nat_lit 0) D2M8K2.u9392 from rfl, allE_node, arows9389, irow9393, arows9392]
  all_goals rfl

theorem atot9393 : totK PD2M8K2 D2M8K2.u9393 = [0, 779950977065, 2861947880287, 2880048588904, 723738840466, 28237008591, 0, 0] := by
  rw [show D2M8K2.u9393 = KTree.node D2M8K2.u9389 (nat_lit 20291112) (nat_lit 3582658539) (nat_lit 0) D2M8K2.u9392 from rfl, totK_node, atot9389, atot9392]
  decide +kernel

theorem arows9400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9400 = true := by
  rw [show D2M8K2.u9400 = KTree.node D2M8K2.u9396 (nat_lit 20297641) (nat_lit 1218212222) (nat_lit 0) D2M8K2.u9399 from rfl, allE_node, arows9396, irow9400, arows9399]
  all_goals rfl

theorem atot9400 : totK PD2M8K2 D2M8K2.u9400 = [0, 916236821138, 3074347372147, 2726034943746, 481268058723, 9915069274, 0, 0] := by
  rw [show D2M8K2.u9400 = KTree.node D2M8K2.u9396 (nat_lit 20297641) (nat_lit 1218212222) (nat_lit 0) D2M8K2.u9399 from rfl, totK_node, atot9396, atot9399]
  decide +kernel

theorem arows9410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9410 = true := by
  rw [show D2M8K2.u9410 = KTree.node D2M8K2.u9406 (nat_lit 20326133) (nat_lit 2212901226) (nat_lit 0) D2M8K2.u9409 from rfl, allE_node, arows9406, irow9410, arows9409]
  all_goals rfl

theorem atot9410 : totK PD2M8K2 D2M8K2.u9410 = [0, 788747289027, 2888235089603, 2830459100387, 626821467741, 25037771093, 0, 0] := by
  rw [show D2M8K2.u9410 = KTree.node D2M8K2.u9406 (nat_lit 20326133) (nat_lit 2212901226) (nat_lit 0) D2M8K2.u9409 from rfl, totK_node, atot9406, atot9409]
  decide +kernel

theorem arows9417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9417 = true := by
  rw [show D2M8K2.u9417 = KTree.node D2M8K2.u9413 (nat_lit 20332833) (nat_lit 1850773156) (nat_lit 0) D2M8K2.u9416 from rfl, allE_node, arows9413, irow9417, arows9416]
  all_goals rfl

theorem atot9417 : totK PD2M8K2 D2M8K2.u9417 = [0, 805213132862, 2882799827126, 2818178816680, 609403614884, 26019340052, 0, 0] := by
  rw [show D2M8K2.u9417 = KTree.node D2M8K2.u9413 (nat_lit 20332833) (nat_lit 1850773156) (nat_lit 0) D2M8K2.u9416 from rfl, totK_node, atot9413, atot9416]
  decide +kernel

theorem arows9425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9425 = true := by
  rw [show D2M8K2.u9425 = KTree.node D2M8K2.u9421 (nat_lit 20343174) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u9424 from rfl, allE_node, arows9421, irow9425, arows9424]
  all_goals rfl

theorem atot9425 : totK PD2M8K2 D2M8K2.u9425 = [0, 180758428870, 1732928477032, 3437286465284, 1557691035040, 141924415987, 1138244013, 0] := by
  rw [show D2M8K2.u9425 = KTree.node D2M8K2.u9421 (nat_lit 20343174) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u9424 from rfl, totK_node, atot9421, atot9424]
  decide +kernel

theorem arows9432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9432 = true := by
  rw [show D2M8K2.u9432 = KTree.node D2M8K2.u9428 (nat_lit 20353945) (nat_lit 1442942970) (nat_lit 0) D2M8K2.u9431 from rfl, allE_node, arows9428, irow9432, arows9431]
  all_goals rfl

theorem atot9432 : totK PD2M8K2 D2M8K2.u9432 = [18947402031, 14643827706, 1236488773429, 3445391140867, 2052366144551, 270649246283, 4977114383, 0] := by
  rw [show D2M8K2.u9432 = KTree.node D2M8K2.u9428 (nat_lit 20353945) (nat_lit 1442942970) (nat_lit 0) D2M8K2.u9431 from rfl, totK_node, atot9428, atot9431]
  decide +kernel

theorem arows9441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9441 = true := by
  rw [show D2M8K2.u9441 = KTree.node D2M8K2.u9437 (nat_lit 20411259) (nat_lit 2883640383) (nat_lit 0) D2M8K2.u9440 from rfl, allE_node, arows9437, irow9441, arows9440]
  all_goals rfl

theorem atot9441 : totK PD2M8K2 D2M8K2.u9441 = [883083547164, 3068259730480, 2692412780098, 499669386553, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u9441 = KTree.node D2M8K2.u9437 (nat_lit 20411259) (nat_lit 2883640383) (nat_lit 0) D2M8K2.u9440 from rfl, totK_node, atot9437, atot9440]
  decide +kernel

theorem arows9448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9448 = true := by
  rw [show D2M8K2.u9448 = KTree.node D2M8K2.u9444 (nat_lit 20418200) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u9447 from rfl, allE_node, arows9444, irow9448, arows9447]
  all_goals rfl

theorem atot9448 : totK PD2M8K2 D2M8K2.u9448 = [896764145289, 2995645048473, 2698388417542, 565595374901, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u9448 = KTree.node D2M8K2.u9444 (nat_lit 20418200) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u9447 from rfl, totK_node, atot9444, atot9447]
  decide +kernel

theorem arows9456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9456 = true := by
  rw [show D2M8K2.u9456 = KTree.node D2M8K2.u9452 (nat_lit 20425709) (nat_lit 1934743799) (nat_lit 0) D2M8K2.u9455 from rfl, allE_node, arows9452, irow9456, arows9455]
  all_goals rfl

theorem atot9456 : totK PD2M8K2 D2M8K2.u9456 = [179867083042, 1592940471869, 3337551534704, 1773364424691, 190684108230, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9456 = KTree.node D2M8K2.u9452 (nat_lit 20425709) (nat_lit 1934743799) (nat_lit 0) D2M8K2.u9455 from rfl, totK_node, atot9452, atot9455]
  decide +kernel

theorem arows9463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9463 = true := by
  rw [show D2M8K2.u9463 = KTree.node D2M8K2.u9459 (nat_lit 20439601) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u9462 from rfl, allE_node, arows9459, irow9463, arows9462]
  all_goals rfl

theorem atot9463 : totK PD2M8K2 D2M8K2.u9463 = [145481999772, 1621477588593, 3597806175162, 1712585343273, 99536752445, 0, 0, 0] := by
  rw [show D2M8K2.u9463 = KTree.node D2M8K2.u9459 (nat_lit 20439601) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u9462 from rfl, totK_node, atot9459, atot9462]
  decide +kernel

theorem arows9475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9475 = true := by
  rw [show D2M8K2.u9475 = KTree.node D2M8K2.u9471 (nat_lit 20452522) (nat_lit 3929323232) (nat_lit 0) D2M8K2.u9474 from rfl, allE_node, arows9471, irow9475, arows9474]
  all_goals rfl

theorem atot9475 : totK PD2M8K2 D2M8K2.u9475 = [718966630480, 2690834499646, 2921503120003, 887613216463, 49495533644, 0, 0, 0] := by
  rw [show D2M8K2.u9475 = KTree.node D2M8K2.u9471 (nat_lit 20452522) (nat_lit 3929323232) (nat_lit 0) D2M8K2.u9474 from rfl, totK_node, atot9471, atot9474]
  decide +kernel

theorem arows9482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9482 = true := by
  rw [show D2M8K2.u9482 = KTree.node D2M8K2.u9478 (nat_lit 20459837) (nat_lit 2292550597) (nat_lit 0) D2M8K2.u9481 from rfl, allE_node, arows9478, irow9482, arows9481]
  all_goals rfl

theorem atot9482 : totK PD2M8K2 D2M8K2.u9482 = [908060238768, 3082894140444, 2777022029312, 549783912510, 17073123161, 0, 0, 0] := by
  rw [show D2M8K2.u9482 = KTree.node D2M8K2.u9478 (nat_lit 20459837) (nat_lit 2292550597) (nat_lit 0) D2M8K2.u9481 from rfl, totK_node, atot9478, atot9481]
  decide +kernel

theorem arows9490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9490 = true := by
  rw [show D2M8K2.u9490 = KTree.node D2M8K2.u9486 (nat_lit 20470459) (nat_lit 1165473726) (nat_lit 0) D2M8K2.u9489 from rfl, allE_node, arows9486, irow9490, arows9489]
  all_goals rfl

theorem atot9490 : totK PD2M8K2 D2M8K2.u9490 = [231056150071, 1498794812729, 2913708993408, 2041908765003, 510331282531, 30397782892, 0, 0] := by
  rw [show D2M8K2.u9490 = KTree.node D2M8K2.u9486 (nat_lit 20470459) (nat_lit 1165473726) (nat_lit 0) D2M8K2.u9489 from rfl, totK_node, atot9486, atot9489]
  decide +kernel

theorem arows9497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9497 = true := by
  rw [show D2M8K2.u9497 = KTree.node D2M8K2.u9493 (nat_lit 20476933) (nat_lit 1293276657) (nat_lit 0) D2M8K2.u9496 from rfl, allE_node, arows9493, irow9497, arows9496]
  all_goals rfl

theorem atot9497 : totK PD2M8K2 D2M8K2.u9497 = [0, 890397539500, 3011935395179, 2752338296095, 584126490992, 16902832282, 0, 0] := by
  rw [show D2M8K2.u9497 = KTree.node D2M8K2.u9493 (nat_lit 20476933) (nat_lit 1293276657) (nat_lit 0) D2M8K2.u9496 from rfl, totK_node, atot9493, atot9496]
  decide +kernel

theorem arows9506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9506 = true := by
  rw [show D2M8K2.u9506 = KTree.node D2M8K2.u9502 (nat_lit 20484577) (nat_lit 1525463237) (nat_lit 0) D2M8K2.u9505 from rfl, allE_node, arows9502, irow9506, arows9505]
  all_goals rfl

theorem atot9506 : totK PD2M8K2 D2M8K2.u9506 = [242856659182, 1265782180523, 2784040192101, 2443178325223, 482889846210, 10717512769, 0, 0] := by
  rw [show D2M8K2.u9506 = KTree.node D2M8K2.u9502 (nat_lit 20484577) (nat_lit 1525463237) (nat_lit 0) D2M8K2.u9505 from rfl, totK_node, atot9502, atot9505]
  decide +kernel

theorem arows9513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9513 = true := by
  rw [show D2M8K2.u9513 = KTree.node D2M8K2.u9509 (nat_lit 20492016) (nat_lit 2688687035) (nat_lit 0) D2M8K2.u9512 from rfl, allE_node, arows9509, irow9513, arows9512]
  all_goals rfl

theorem atot9513 : totK PD2M8K2 D2M8K2.u9513 = [822539972619, 2829806769587, 2812700438664, 773634520225, 38930019324, 0, 0, 0] := by
  rw [show D2M8K2.u9513 = KTree.node D2M8K2.u9509 (nat_lit 20492016) (nat_lit 2688687035) (nat_lit 0) D2M8K2.u9512 from rfl, totK_node, atot9509, atot9512]
  decide +kernel

theorem arows9521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9521 = true := by
  rw [show D2M8K2.u9521 = KTree.node D2M8K2.u9517 (nat_lit 20505057) (nat_lit 1687920405) (nat_lit 0) D2M8K2.u9520 from rfl, allE_node, arows9517, irow9521, arows9520]
  all_goals rfl

theorem atot9521 : totK PD2M8K2 D2M8K2.u9521 = [588190532914, 2610845861180, 3111876947789, 859758189848, 36462486507, 0, 0, 0] := by
  rw [show D2M8K2.u9521 = KTree.node D2M8K2.u9517 (nat_lit 20505057) (nat_lit 1687920405) (nat_lit 0) D2M8K2.u9520 from rfl, totK_node, atot9517, atot9520]
  decide +kernel

theorem arows9528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9528 = true := by
  rw [show D2M8K2.u9528 = KTree.node D2M8K2.u9524 (nat_lit 20512395) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u9527 from rfl, allE_node, arows9524, irow9528, arows9527]
  all_goals rfl

theorem atot9528 : totK PD2M8K2 D2M8K2.u9528 = [0, 1083492529047, 3396153354943, 2372382530851, 277701472720, 2369401571, 0, 0] := by
  rw [show D2M8K2.u9528 = KTree.node D2M8K2.u9524 (nat_lit 20512395) (nat_lit 3736031856) (nat_lit 0) D2M8K2.u9527 from rfl, totK_node, atot9524, atot9527]
  decide +kernel

theorem arows9538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9538 = true := by
  rw [show D2M8K2.u9538 = KTree.node D2M8K2.u9534 (nat_lit 20529320) (nat_lit 3697579784) (nat_lit 0) D2M8K2.u9537 from rfl, allE_node, arows9534, irow9538, arows9537]
  all_goals rfl

theorem atot9538 : totK PD2M8K2 D2M8K2.u9538 = [569752760700, 2282553260696, 2810668904796, 1275877708032, 235422376750, 11853261585, 0, 0] := by
  rw [show D2M8K2.u9538 = KTree.node D2M8K2.u9534 (nat_lit 20529320) (nat_lit 3697579784) (nat_lit 0) D2M8K2.u9537 from rfl, totK_node, atot9534, atot9537]
  decide +kernel

theorem arows9545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9545 = true := by
  rw [show D2M8K2.u9545 = KTree.node D2M8K2.u9541 (nat_lit 20539174) (nat_lit 2861108828) (nat_lit 0) D2M8K2.u9544 from rfl, allE_node, arows9541, irow9545, arows9544]
  all_goals rfl

theorem atot9545 : totK PD2M8K2 D2M8K2.u9545 = [710139211025, 2659373959562, 2948694147589, 919329793353, 50659546952, 0, 0, 0] := by
  rw [show D2M8K2.u9545 = KTree.node D2M8K2.u9541 (nat_lit 20539174) (nat_lit 2861108828) (nat_lit 0) D2M8K2.u9544 from rfl, totK_node, atot9541, atot9544]
  decide +kernel

theorem arows9553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9553 = true := by
  rw [show D2M8K2.u9553 = KTree.node D2M8K2.u9549 (nat_lit 20546410) (nat_lit 3915448483) (nat_lit 0) D2M8K2.u9552 from rfl, allE_node, arows9549, irow9553, arows9552]
  all_goals rfl

theorem atot9553 : totK PD2M8K2 D2M8K2.u9553 = [756603494842, 2827765878850, 2910371561394, 723600884364, 28392472652, 0, 0, 0] := by
  rw [show D2M8K2.u9553 = KTree.node D2M8K2.u9549 (nat_lit 20546410) (nat_lit 3915448483) (nat_lit 0) D2M8K2.u9552 from rfl, totK_node, atot9549, atot9552]
  decide +kernel

theorem arows9560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9560 = true := by
  rw [show D2M8K2.u9560 = KTree.node D2M8K2.u9556 (nat_lit 20553668) (nat_lit 3205819489) (nat_lit 0) D2M8K2.u9559 from rfl, allE_node, arows9556, irow9560, arows9559]
  all_goals rfl

theorem atot9560 : totK PD2M8K2 D2M8K2.u9560 = [0, 1175638845827, 3506359009365, 2286151800704, 221471163387, 1239866073, 0, 0] := by
  rw [show D2M8K2.u9560 = KTree.node D2M8K2.u9556 (nat_lit 20553668) (nat_lit 3205819489) (nat_lit 0) D2M8K2.u9559 from rfl, totK_node, atot9556, atot9559]
  decide +kernel

theorem arows9569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9569 = true := by
  rw [show D2M8K2.u9569 = KTree.node D2M8K2.u9565 (nat_lit 20565320) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u9568 from rfl, allE_node, arows9565, irow9569, arows9568]
  all_goals rfl

theorem atot9569 : totK PD2M8K2 D2M8K2.u9569 = [174434339562, 1194702620283, 2848148636238, 2407918438167, 485907659467, 17826068843, 0, 0] := by
  rw [show D2M8K2.u9569 = KTree.node D2M8K2.u9565 (nat_lit 20565320) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u9568 from rfl, totK_node, atot9565, atot9568]
  decide +kernel

theorem arows9576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9576 = true := by
  rw [show D2M8K2.u9576 = KTree.node D2M8K2.u9572 (nat_lit 20615995) (nat_lit 2241415799) (nat_lit 0) D2M8K2.u9575 from rfl, allE_node, arows9572, irow9576, arows9575]
  all_goals rfl

theorem atot9576 : totK PD2M8K2 D2M8K2.u9576 = [774263411875, 2808052350603, 2841316563920, 764219768164, 38740156794, 0, 0, 0] := by
  rw [show D2M8K2.u9576 = KTree.node D2M8K2.u9572 (nat_lit 20615995) (nat_lit 2241415799) (nat_lit 0) D2M8K2.u9575 from rfl, totK_node, atot9572, atot9575]
  decide +kernel

theorem arows9584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9584 = true := by
  rw [show D2M8K2.u9584 = KTree.node D2M8K2.u9580 (nat_lit 20622314) (nat_lit 4129241511) (nat_lit 0) D2M8K2.u9583 from rfl, allE_node, arows9580, irow9584, arows9583]
  all_goals rfl

theorem atot9584 : totK PD2M8K2 D2M8K2.u9584 = [798698211926, 2890087280432, 2849588641518, 644510534276, 23676876901, 0, 0, 0] := by
  rw [show D2M8K2.u9584 = KTree.node D2M8K2.u9580 (nat_lit 20622314) (nat_lit 4129241511) (nat_lit 0) D2M8K2.u9583 from rfl, totK_node, atot9580, atot9583]
  decide +kernel

theorem arows9591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9591 = true := by
  rw [show D2M8K2.u9591 = KTree.node D2M8K2.u9587 (nat_lit 20632198) (nat_lit 3475580784) (nat_lit 0) D2M8K2.u9590 from rfl, allE_node, arows9587, irow9591, arows9590]
  all_goals rfl

theorem atot9591 : totK PD2M8K2 D2M8K2.u9591 = [360495417397, 1879361542016, 3141349872685, 1646767240326, 154620930482, 1310285577, 0, 0] := by
  rw [show D2M8K2.u9591 = KTree.node D2M8K2.u9587 (nat_lit 20632198) (nat_lit 3475580784) (nat_lit 0) D2M8K2.u9590 from rfl, totK_node, atot9587, atot9590]
  decide +kernel

theorem arows9602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9602 = true := by
  rw [show D2M8K2.u9602 = KTree.node D2M8K2.u9598 (nat_lit 20640718) (nat_lit 3998384852) (nat_lit 0) D2M8K2.u9601 from rfl, allE_node, arows9598, irow9602, arows9601]
  all_goals rfl

theorem atot9602 : totK PD2M8K2 D2M8K2.u9602 = [0, 1170290025410, 3410530614599, 2312048407768, 291346509053, 4879840392, 0, 0] := by
  rw [show D2M8K2.u9602 = KTree.node D2M8K2.u9598 (nat_lit 20640718) (nat_lit 3998384852) (nat_lit 0) D2M8K2.u9601 from rfl, totK_node, atot9598, atot9601]
  decide +kernel

theorem arows9609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9609 = true := by
  rw [show D2M8K2.u9609 = KTree.node D2M8K2.u9605 (nat_lit 20651265) (nat_lit 1351421296) (nat_lit 0) D2M8K2.u9608 from rfl, allE_node, arows9605, irow9609, arows9608]
  all_goals rfl

theorem atot9609 : totK PD2M8K2 D2M8K2.u9609 = [0, 797770852802, 2919350570237, 2762673314953, 617975878959, 26682572712, 0, 0] := by
  rw [show D2M8K2.u9609 = KTree.node D2M8K2.u9605 (nat_lit 20651265) (nat_lit 1351421296) (nat_lit 0) D2M8K2.u9608 from rfl, totK_node, atot9605, atot9608]
  decide +kernel

theorem arows9617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9617 = true := by
  rw [show D2M8K2.u9617 = KTree.node D2M8K2.u9613 (nat_lit 20661631) (nat_lit 2263374186) (nat_lit 0) D2M8K2.u9616 from rfl, allE_node, arows9613, irow9617, arows9616]
  all_goals rfl

theorem atot9617 : totK PD2M8K2 D2M8K2.u9617 = [0, 873237418795, 3112079130150, 2767297268025, 441569615143, 6541958310, 0, 0] := by
  rw [show D2M8K2.u9617 = KTree.node D2M8K2.u9613 (nat_lit 20661631) (nat_lit 2263374186) (nat_lit 0) D2M8K2.u9616 from rfl, totK_node, atot9613, atot9616]
  decide +kernel

theorem arows9624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9624 = true := by
  rw [show D2M8K2.u9624 = KTree.node D2M8K2.u9620 (nat_lit 20669582) (nat_lit 3178870039) (nat_lit 0) D2M8K2.u9623 from rfl, allE_node, arows9620, irow9624, arows9623]
  all_goals rfl

theorem atot9624 : totK PD2M8K2 D2M8K2.u9624 = [0, 749348375738, 2900298850394, 2909019808439, 562785446508, 11227377586, 0, 0] := by
  rw [show D2M8K2.u9624 = KTree.node D2M8K2.u9620 (nat_lit 20669582) (nat_lit 3178870039) (nat_lit 0) D2M8K2.u9623 from rfl, totK_node, atot9620, atot9623]
  decide +kernel

theorem arows9633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9633 = true := by
  rw [show D2M8K2.u9633 = KTree.node D2M8K2.u9629 (nat_lit 20676702) (nat_lit 3355456870) (nat_lit 0) D2M8K2.u9632 from rfl, allE_node, arows9629, irow9633, arows9632]
  all_goals rfl

theorem atot9633 : totK PD2M8K2 D2M8K2.u9633 = [0, 0, 1249804191133, 3598240395182, 1976645117292, 167712409987, 1369150432, 0] := by
  rw [show D2M8K2.u9633 = KTree.node D2M8K2.u9629 (nat_lit 20676702) (nat_lit 3355456870) (nat_lit 0) D2M8K2.u9632 from rfl, totK_node, atot9629, atot9632]
  decide +kernel

theorem arows9640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9640 = true := by
  rw [show D2M8K2.u9640 = KTree.node D2M8K2.u9636 (nat_lit 20692543) (nat_lit 2248039224) (nat_lit 0) D2M8K2.u9639 from rfl, allE_node, arows9636, irow9640, arows9639]
  all_goals rfl

theorem atot9640 : totK PD2M8K2 D2M8K2.u9640 = [0, 442893429356, 2173690715442, 3254277296377, 1233414847649, 68436072493, 0, 0] := by
  rw [show D2M8K2.u9640 = KTree.node D2M8K2.u9636 (nat_lit 20692543) (nat_lit 2248039224) (nat_lit 0) D2M8K2.u9639 from rfl, totK_node, atot9636, atot9639]
  decide +kernel

theorem arows9648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9648 = true := by
  rw [show D2M8K2.u9648 = KTree.node D2M8K2.u9644 (nat_lit 20703748) (nat_lit 3866437580) (nat_lit 0) D2M8K2.u9647 from rfl, allE_node, arows9644, irow9648, arows9647]
  all_goals rfl

theorem atot9648 : totK PD2M8K2 D2M8K2.u9648 = [0, 802583789356, 2854178669253, 2872765759230, 717456578035, 22399447327, 0, 0] := by
  rw [show D2M8K2.u9648 = KTree.node D2M8K2.u9644 (nat_lit 20703748) (nat_lit 3866437580) (nat_lit 0) D2M8K2.u9647 from rfl, totK_node, atot9644, atot9647]
  decide +kernel

theorem arows9655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9655 = true := by
  rw [show D2M8K2.u9655 = KTree.node D2M8K2.u9651 (nat_lit 20711454) (nat_lit 3860568084) (nat_lit 0) D2M8K2.u9654 from rfl, allE_node, arows9651, irow9655, arows9654]
  all_goals rfl

theorem atot9655 : totK PD2M8K2 D2M8K2.u9655 = [0, 757254340034, 2849963609930, 2949445645761, 678940891748, 18048198057, 0, 0] := by
  rw [show D2M8K2.u9655 = KTree.node D2M8K2.u9651 (nat_lit 20711454) (nat_lit 3860568084) (nat_lit 0) D2M8K2.u9654 from rfl, totK_node, atot9651, atot9654]
  decide +kernel

theorem arows9665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9665 = true := by
  rw [show D2M8K2.u9665 = KTree.node D2M8K2.u9661 (nat_lit 20739294) (nat_lit 3812338242) (nat_lit 0) D2M8K2.u9664 from rfl, allE_node, arows9661, irow9665, arows9664]
  all_goals rfl

theorem atot9665 : totK PD2M8K2 D2M8K2.u9665 = [0, 803865266991, 2857793016978, 2793831053177, 720398112775, 39389821520, 0, 0] := by
  rw [show D2M8K2.u9665 = KTree.node D2M8K2.u9661 (nat_lit 20739294) (nat_lit 3812338242) (nat_lit 0) D2M8K2.u9664 from rfl, totK_node, atot9661, atot9664]
  decide +kernel

theorem arows9672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9672 = true := by
  rw [show D2M8K2.u9672 = KTree.node D2M8K2.u9668 (nat_lit 20745469) (nat_lit 976806065) (nat_lit 0) D2M8K2.u9671 from rfl, allE_node, arows9668, irow9672, arows9671]
  all_goals rfl

theorem atot9672 : totK PD2M8K2 D2M8K2.u9672 = [0, 852487817410, 2951647487086, 2765495830097, 628564029591, 22391977957, 0, 0] := by
  rw [show D2M8K2.u9672 = KTree.node D2M8K2.u9668 (nat_lit 20745469) (nat_lit 976806065) (nat_lit 0) D2M8K2.u9671 from rfl, totK_node, atot9668, atot9671]
  decide +kernel

theorem arows9680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9680 = true := by
  rw [show D2M8K2.u9680 = KTree.node D2M8K2.u9676 (nat_lit 20759627) (nat_lit 2077389013) (nat_lit 0) D2M8K2.u9679 from rfl, allE_node, arows9676, irow9680, arows9679]
  all_goals rfl

theorem atot9680 : totK PD2M8K2 D2M8K2.u9680 = [0, 0, 1330781685265, 3627396054283, 1964933178643, 154506185227, 1166720416, 0] := by
  rw [show D2M8K2.u9680 = KTree.node D2M8K2.u9676 (nat_lit 20759627) (nat_lit 2077389013) (nat_lit 0) D2M8K2.u9679 from rfl, totK_node, atot9676, atot9679]
  decide +kernel

theorem arows9687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9687 = true := by
  rw [show D2M8K2.u9687 = KTree.node D2M8K2.u9683 (nat_lit 20775657) (nat_lit 1138190782) (nat_lit 0) D2M8K2.u9686 from rfl, allE_node, arows9683, irow9687, arows9686]
  all_goals rfl

theorem atot9687 : totK PD2M8K2 D2M8K2.u9687 = [0, 496401116654, 2040752277741, 2880011439562, 1474313060120, 208805719751, 5134755853, 0] := by
  rw [show D2M8K2.u9687 = KTree.node D2M8K2.u9683 (nat_lit 20775657) (nat_lit 1138190782) (nat_lit 0) D2M8K2.u9686 from rfl, totK_node, atot9683, atot9686]
  decide +kernel

theorem arows9696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9696 = true := by
  rw [show D2M8K2.u9696 = KTree.node D2M8K2.u9692 (nat_lit 20784166) (nat_lit 3815620521) (nat_lit 0) D2M8K2.u9695 from rfl, allE_node, arows9692, irow9696, arows9695]
  all_goals rfl

theorem atot9696 : totK PD2M8K2 D2M8K2.u9696 = [0, 767457096527, 2800792217018, 2846452473775, 817836603925, 42474320767, 0, 0] := by
  rw [show D2M8K2.u9696 = KTree.node D2M8K2.u9692 (nat_lit 20784166) (nat_lit 3815620521) (nat_lit 0) D2M8K2.u9695 from rfl, totK_node, atot9692, atot9695]
  decide +kernel

theorem arows9703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9703 = true := by
  rw [show D2M8K2.u9703 = KTree.node D2M8K2.u9699 (nat_lit 20794882) (nat_lit 4142126202) (nat_lit 0) D2M8K2.u9702 from rfl, allE_node, arows9699, irow9703, arows9702]
  all_goals rfl

theorem atot9703 : totK PD2M8K2 D2M8K2.u9703 = [0, 769917351693, 2870432955813, 2906626718186, 640567192924, 18308814581, 0, 0] := by
  rw [show D2M8K2.u9703 = KTree.node D2M8K2.u9699 (nat_lit 20794882) (nat_lit 4142126202) (nat_lit 0) D2M8K2.u9702 from rfl, totK_node, atot9699, atot9702]
  decide +kernel

theorem arows9711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9711 = true := by
  rw [show D2M8K2.u9711 = KTree.node D2M8K2.u9707 (nat_lit 20802266) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u9710 from rfl, allE_node, arows9707, irow9711, arows9710]
  all_goals rfl

theorem atot9711 : totK PD2M8K2 D2M8K2.u9711 = [0, 0, 1247531153353, 3492482947648, 2114437731648, 206825168953, 2335892675, 0] := by
  rw [show D2M8K2.u9711 = KTree.node D2M8K2.u9707 (nat_lit 20802266) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u9710 from rfl, totK_node, atot9707, atot9710]
  decide +kernel

theorem arows9718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9718 = true := by
  rw [show D2M8K2.u9718 = KTree.node D2M8K2.u9714 (nat_lit 20816518) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u9717 from rfl, allE_node, arows9714, irow9718, arows9717]
  all_goals rfl

theorem atot9718 : totK PD2M8K2 D2M8K2.u9718 = [0, 413512698075, 2109204749098, 3077420381751, 1335799400789, 158772559968, 4028038878, 0] := by
  rw [show D2M8K2.u9718 = KTree.node D2M8K2.u9714 (nat_lit 20816518) (nat_lit 2494477528) (nat_lit 0) D2M8K2.u9717 from rfl, totK_node, atot9714, atot9717]
  decide +kernel

theorem arows9731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9731 = true := by
  rw [show D2M8K2.u9731 = KTree.node D2M8K2.u9727 (nat_lit 20866602) (nat_lit 3850059356) (nat_lit 0) D2M8K2.u9730 from rfl, allE_node, arows9727, irow9731, arows9730]
  all_goals rfl

theorem atot9731 : totK PD2M8K2 D2M8K2.u9731 = [0, 826845934660, 2857607771184, 2788552738639, 716962613471, 31571751909, 0, 0] := by
  rw [show D2M8K2.u9731 = KTree.node D2M8K2.u9727 (nat_lit 20866602) (nat_lit 3850059356) (nat_lit 0) D2M8K2.u9730 from rfl, totK_node, atot9727, atot9730]
  decide +kernel

theorem arows9738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9738 = true := by
  rw [show D2M8K2.u9738 = KTree.node D2M8K2.u9734 (nat_lit 20873392) (nat_lit 2178735802) (nat_lit 0) D2M8K2.u9737 from rfl, allE_node, arows9734, irow9738, arows9737]
  all_goals rfl

theorem atot9738 : totK PD2M8K2 D2M8K2.u9738 = [0, 869732732092, 2955033721580, 2777274427387, 602890870586, 17318704994, 0, 0] := by
  rw [show D2M8K2.u9738 = KTree.node D2M8K2.u9734 (nat_lit 20873392) (nat_lit 2178735802) (nat_lit 0) D2M8K2.u9737 from rfl, totK_node, atot9734, atot9737]
  decide +kernel

theorem arows9746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9746 = true := by
  rw [show D2M8K2.u9746 = KTree.node D2M8K2.u9742 (nat_lit 20882976) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u9745 from rfl, allE_node, arows9742, irow9746, arows9745]
  all_goals rfl

theorem atot9746 : totK PD2M8K2 D2M8K2.u9746 = [0, 0, 1335288079778, 3558783046610, 1994253074881, 188674841477, 1288491354, 0] := by
  rw [show D2M8K2.u9746 = KTree.node D2M8K2.u9742 (nat_lit 20882976) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u9745 from rfl, totK_node, atot9742, atot9745]
  decide +kernel

theorem arows9753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9753 = true := by
  rw [show D2M8K2.u9753 = KTree.node D2M8K2.u9749 (nat_lit 20892515) (nat_lit 2952766762) (nat_lit 0) D2M8K2.u9752 from rfl, allE_node, arows9749, irow9753, arows9752]
  all_goals rfl

theorem atot9753 : totK PD2M8K2 D2M8K2.u9753 = [0, 0, 942722609322, 3166277400662, 2505535208456, 392077899966, 9625297583, 0] := by
  rw [show D2M8K2.u9753 = KTree.node D2M8K2.u9749 (nat_lit 20892515) (nat_lit 2952766762) (nat_lit 0) D2M8K2.u9752 from rfl, totK_node, atot9749, atot9752]
  decide +kernel

theorem arows9762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9762 = true := by
  rw [show D2M8K2.u9762 = KTree.node D2M8K2.u9758 (nat_lit 20902827) (nat_lit 3396739419) (nat_lit 0) D2M8K2.u9761 from rfl, allE_node, arows9758, irow9762, arows9761]
  all_goals rfl

theorem atot9762 : totK PD2M8K2 D2M8K2.u9762 = [0, 672581978995, 2274393205248, 2427056749763, 1397218947180, 388266525689, 21751168066, 0] := by
  rw [show D2M8K2.u9762 = KTree.node D2M8K2.u9758 (nat_lit 20902827) (nat_lit 3396739419) (nat_lit 0) D2M8K2.u9761 from rfl, totK_node, atot9758, atot9761]
  decide +kernel

theorem arows9769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9769 = true := by
  rw [show D2M8K2.u9769 = KTree.node D2M8K2.u9765 (nat_lit 20913337) (nat_lit 1438466239) (nat_lit 0) D2M8K2.u9768 from rfl, allE_node, arows9765, irow9769, arows9768]
  all_goals rfl

theorem atot9769 : totK PD2M8K2 D2M8K2.u9769 = [0, 814501505429, 2842538952884, 2800530857985, 640739886162, 26300412495, 0, 0] := by
  rw [show D2M8K2.u9769 = KTree.node D2M8K2.u9765 (nat_lit 20913337) (nat_lit 1438466239) (nat_lit 0) D2M8K2.u9768 from rfl, totK_node, atot9765, atot9768]
  decide +kernel

theorem arows9777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9777 = true := by
  rw [show D2M8K2.u9777 = KTree.node D2M8K2.u9773 (nat_lit 20919918) (nat_lit 2556776182) (nat_lit 0) D2M8K2.u9776 from rfl, allE_node, arows9773, irow9777, arows9776]
  all_goals rfl

theorem atot9777 : totK PD2M8K2 D2M8K2.u9777 = [0, 609933941819, 2638383221883, 3069586625007, 787855763936, 29551679099, 0, 0] := by
  rw [show D2M8K2.u9777 = KTree.node D2M8K2.u9773 (nat_lit 20919918) (nat_lit 2556776182) (nat_lit 0) D2M8K2.u9776 from rfl, totK_node, atot9773, atot9776]
  decide +kernel

theorem arows9784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9784 = true := by
  rw [show D2M8K2.u9784 = KTree.node D2M8K2.u9780 (nat_lit 20930268) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u9783 from rfl, allE_node, arows9780, irow9784, arows9783]
  all_goals rfl

theorem atot9784 : totK PD2M8K2 D2M8K2.u9784 = [0, 0, 1226253830908, 3537495544512, 2071140721750, 212398287095, 1369150432, 0] := by
  rw [show D2M8K2.u9784 = KTree.node D2M8K2.u9780 (nat_lit 20930268) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u9783 from rfl, totK_node, atot9780, atot9783]
  decide +kernel

theorem arows9794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9794 = true := by
  rw [show D2M8K2.u9794 = KTree.node D2M8K2.u9790 (nat_lit 20984914) (nat_lit 3824121436) (nat_lit 0) D2M8K2.u9793 from rfl, allE_node, arows9790, irow9794, arows9793]
  all_goals rfl

theorem atot9794 : totK PD2M8K2 D2M8K2.u9794 = [0, 507873920842, 2377500659474, 3147554959359, 1045882021114, 50556943091, 0, 0] := by
  rw [show D2M8K2.u9794 = KTree.node D2M8K2.u9790 (nat_lit 20984914) (nat_lit 3824121436) (nat_lit 0) D2M8K2.u9793 from rfl, totK_node, atot9790, atot9793]
  decide +kernel

theorem arows9801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9801 = true := by
  rw [show D2M8K2.u9801 = KTree.node D2M8K2.u9797 (nat_lit 20998795) (nat_lit 1416984630) (nat_lit 0) D2M8K2.u9800 from rfl, allE_node, arows9797, irow9801, arows9800]
  all_goals rfl

theorem atot9801 : totK PD2M8K2 D2M8K2.u9801 = [0, 865543070637, 2987076604067, 2769531204941, 536648949572, 18030242193, 0, 0] := by
  rw [show D2M8K2.u9801 = KTree.node D2M8K2.u9797 (nat_lit 20998795) (nat_lit 1416984630) (nat_lit 0) D2M8K2.u9800 from rfl, totK_node, atot9797, atot9800]
  decide +kernel

theorem arows9809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9809 = true := by
  rw [show D2M8K2.u9809 = KTree.node D2M8K2.u9805 (nat_lit 21006188) (nat_lit 3475960255) (nat_lit 0) D2M8K2.u9808 from rfl, allE_node, arows9805, irow9809, arows9808]
  all_goals rfl

theorem atot9809 : totK PD2M8K2 D2M8K2.u9809 = [0, 274734738259, 1817130716469, 3332771655457, 1560973108872, 135508902917, 1206465782, 0] := by
  rw [show D2M8K2.u9809 = KTree.node D2M8K2.u9805 (nat_lit 21006188) (nat_lit 3475960255) (nat_lit 0) D2M8K2.u9808 from rfl, totK_node, atot9805, atot9808]
  decide +kernel

theorem arows9816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9816 = true := by
  rw [show D2M8K2.u9816 = KTree.node D2M8K2.u9812 (nat_lit 21023338) (nat_lit 3935621357) (nat_lit 0) D2M8K2.u9815 from rfl, allE_node, arows9812, irow9816, arows9815]
  all_goals rfl

theorem atot9816 : totK PD2M8K2 D2M8K2.u9816 = [0, 421502549754, 2130716664322, 3227979633137, 1294944338163, 69893382862, 0, 0] := by
  rw [show D2M8K2.u9816 = KTree.node D2M8K2.u9812 (nat_lit 21023338) (nat_lit 3935621357) (nat_lit 0) D2M8K2.u9815 from rfl, totK_node, atot9812, atot9815]
  decide +kernel

theorem arows9825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9825 = true := by
  rw [show D2M8K2.u9825 = KTree.node D2M8K2.u9821 (nat_lit 21032531) (nat_lit 2580767063) (nat_lit 0) D2M8K2.u9824 from rfl, allE_node, arows9821, irow9825, arows9824]
  all_goals rfl

theorem atot9825 : totK PD2M8K2 D2M8K2.u9825 = [0, 788466830046, 2857950176129, 2906392926491, 740056918280, 32501519404, 0, 0] := by
  rw [show D2M8K2.u9825 = KTree.node D2M8K2.u9821 (nat_lit 21032531) (nat_lit 2580767063) (nat_lit 0) D2M8K2.u9824 from rfl, totK_node, atot9821, atot9824]
  decide +kernel

theorem arows9832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9832 = true := by
  rw [show D2M8K2.u9832 = KTree.node D2M8K2.u9828 (nat_lit 21042183) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u9831 from rfl, allE_node, arows9828, irow9832, arows9831]
  all_goals rfl

theorem atot9832 : totK PD2M8K2 D2M8K2.u9832 = [0, 824892594861, 2943362055662, 2829993321769, 589000586482, 18301866131, 0, 0] := by
  rw [show D2M8K2.u9832 = KTree.node D2M8K2.u9828 (nat_lit 21042183) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u9831 from rfl, totK_node, atot9828, atot9831]
  decide +kernel

theorem arows9840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9840 = true := by
  rw [show D2M8K2.u9840 = KTree.node D2M8K2.u9836 (nat_lit 21048992) (nat_lit 3250758232) (nat_lit 0) D2M8K2.u9839 from rfl, allE_node, arows9836, irow9840, arows9839]
  all_goals rfl

theorem atot9840 : totK PD2M8K2 D2M8K2.u9840 = [0, 0, 1280700514232, 3574256966015, 2131769007092, 198254415914, 1239866073, 0] := by
  rw [show D2M8K2.u9840 = KTree.node D2M8K2.u9836 (nat_lit 21048992) (nat_lit 3250758232) (nat_lit 0) D2M8K2.u9839 from rfl, totK_node, atot9836, atot9839]
  decide +kernel

theorem arows9847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9847 = true := by
  rw [show D2M8K2.u9847 = KTree.node D2M8K2.u9843 (nat_lit 21061458) (nat_lit 2435173938) (nat_lit 0) D2M8K2.u9846 from rfl, allE_node, arows9843, irow9847, arows9846]
  all_goals rfl

theorem atot9847 : totK PD2M8K2 D2M8K2.u9847 = [0, 0, 847972607005, 3046744827483, 2635675482357, 491288106124, 17826068843, 0] := by
  rw [show D2M8K2.u9847 = KTree.node D2M8K2.u9843 (nat_lit 21061458) (nat_lit 2435173938) (nat_lit 0) D2M8K2.u9846 from rfl, totK_node, atot9843, atot9846]
  decide +kernel

theorem arows9858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9858 = true := by
  rw [show D2M8K2.u9858 = KTree.node D2M8K2.u9854 (nat_lit 21070372) (nat_lit 2796028262) (nat_lit 0) D2M8K2.u9857 from rfl, allE_node, arows9854, irow9858, arows9857]
  all_goals rfl

theorem atot9858 : totK PD2M8K2 D2M8K2.u9858 = [0, 748455029272, 2825891337239, 2870577529843, 769012508503, 36729083492, 0, 0] := by
  rw [show D2M8K2.u9858 = KTree.node D2M8K2.u9854 (nat_lit 21070372) (nat_lit 2796028262) (nat_lit 0) D2M8K2.u9857 from rfl, totK_node, atot9854, atot9857]
  decide +kernel

theorem arows9865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9865 = true := by
  rw [show D2M8K2.u9865 = KTree.node D2M8K2.u9861 (nat_lit 21078164) (nat_lit 3239882713) (nat_lit 0) D2M8K2.u9864 from rfl, allE_node, arows9861, irow9865, arows9864]
  all_goals rfl

theorem atot9865 : totK PD2M8K2 D2M8K2.u9865 = [0, 794107553641, 2802938605433, 2839867340860, 687441674340, 27709973308, 0, 0] := by
  rw [show D2M8K2.u9865 = KTree.node D2M8K2.u9861 (nat_lit 21078164) (nat_lit 3239882713) (nat_lit 0) D2M8K2.u9864 from rfl, totK_node, atot9861, atot9864]
  decide +kernel

theorem arows9873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9873 = true := by
  rw [show D2M8K2.u9873 = KTree.node D2M8K2.u9869 (nat_lit 21084704) (nat_lit 3728389748) (nat_lit 0) D2M8K2.u9872 from rfl, allE_node, arows9869, irow9873, arows9872]
  all_goals rfl

theorem atot9873 : totK PD2M8K2 D2M8K2.u9873 = [0, 435349895630, 2057738679459, 3107499479213, 1384610733845, 126325595580, 1138244013, 0] := by
  rw [show D2M8K2.u9873 = KTree.node D2M8K2.u9869 (nat_lit 21084704) (nat_lit 3728389748) (nat_lit 0) D2M8K2.u9872 from rfl, totK_node, atot9869, atot9872]
  decide +kernel

theorem arows9880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9880 = true := by
  rw [show D2M8K2.u9880 = KTree.node D2M8K2.u9876 (nat_lit 21099396) (nat_lit 1519051010) (nat_lit 0) D2M8K2.u9879 from rfl, allE_node, arows9876, irow9880, arows9879]
  all_goals rfl

theorem atot9880 : totK PD2M8K2 D2M8K2.u9880 = [0, 0, 1456402416267, 3794813581728, 1778644270985, 101452664822, 0, 0] := by
  rw [show D2M8K2.u9880 = KTree.node D2M8K2.u9876 (nat_lit 21099396) (nat_lit 1519051010) (nat_lit 0) D2M8K2.u9879 from rfl, totK_node, atot9876, atot9879]
  decide +kernel

theorem arows9889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9889 = true := by
  rw [show D2M8K2.u9889 = KTree.node D2M8K2.u9885 (nat_lit 21111250) (nat_lit 3972028027) (nat_lit 0) D2M8K2.u9888 from rfl, allE_node, arows9885, irow9889, arows9888]
  all_goals rfl

theorem atot9889 : totK PD2M8K2 D2M8K2.u9889 = [0, 752300002680, 2587864041619, 2628599133151, 1060628394353, 179513351685, 4977114383, 0] := by
  rw [show D2M8K2.u9889 = KTree.node D2M8K2.u9885 (nat_lit 21111250) (nat_lit 3972028027) (nat_lit 0) D2M8K2.u9888 from rfl, totK_node, atot9885, atot9888]
  decide +kernel

theorem arows9896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9896 = true := by
  rw [show D2M8K2.u9896 = KTree.node D2M8K2.u9892 (nat_lit 21119143) (nat_lit 2026008224) (nat_lit 0) D2M8K2.u9895 from rfl, allE_node, arows9892, irow9896, arows9895]
  all_goals rfl

theorem atot9896 : totK PD2M8K2 D2M8K2.u9896 = [0, 797056638845, 2837979583309, 2868154530311, 703961336496, 25872693616, 0, 0] := by
  rw [show D2M8K2.u9896 = KTree.node D2M8K2.u9892 (nat_lit 21119143) (nat_lit 2026008224) (nat_lit 0) D2M8K2.u9895 from rfl, totK_node, atot9892, atot9895]
  decide +kernel

theorem arows9904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9904 = true := by
  rw [show D2M8K2.u9904 = KTree.node D2M8K2.u9900 (nat_lit 21129138) (nat_lit 3415029130) (nat_lit 0) D2M8K2.u9903 from rfl, allE_node, arows9900, irow9904, arows9903]
  all_goals rfl

theorem atot9904 : totK PD2M8K2 D2M8K2.u9904 = [0, 439710514742, 2072194004471, 3117768785145, 1401235540275, 126683019516, 1310285577, 0] := by
  rw [show D2M8K2.u9904 = KTree.node D2M8K2.u9900 (nat_lit 21129138) (nat_lit 3415029130) (nat_lit 0) D2M8K2.u9903 from rfl, totK_node, atot9900, atot9903]
  decide +kernel

theorem arows9911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9911 = true := by
  rw [show D2M8K2.u9911 = KTree.node D2M8K2.u9907 (nat_lit 21138356) (nat_lit 2428375572) (nat_lit 0) D2M8K2.u9910 from rfl, allE_node, arows9907, irow9911, arows9910]
  all_goals rfl

theorem atot9911 : totK PD2M8K2 D2M8K2.u9911 = [0, 0, 1126028489308, 3404235368561, 2385935340807, 282185681293, 4931404646, 0] := by
  rw [show D2M8K2.u9911 = KTree.node D2M8K2.u9907 (nat_lit 21138356) (nat_lit 2428375572) (nat_lit 0) D2M8K2.u9910 from rfl, totK_node, atot9907, atot9910]
  decide +kernel

theorem arows9921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9921 = true := by
  rw [show D2M8K2.u9921 = KTree.node D2M8K2.u9917 (nat_lit 21150510) (nat_lit 4020990476) (nat_lit 0) D2M8K2.u9920 from rfl, allE_node, arows9917, irow9921, arows9920]
  all_goals rfl

theorem atot9921 : totK PD2M8K2 D2M8K2.u9921 = [0, 0, 878057443554, 3109654360363, 2719766710388, 485644744222, 15221454336, 0] := by
  rw [show D2M8K2.u9921 = KTree.node D2M8K2.u9917 (nat_lit 21150510) (nat_lit 4020990476) (nat_lit 0) D2M8K2.u9920 from rfl, totK_node, atot9917, atot9920]
  decide +kernel

theorem arows9928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9928 = true := by
  rw [show D2M8K2.u9928 = KTree.node D2M8K2.u9924 (nat_lit 21161420) (nat_lit 3300260735) (nat_lit 0) D2M8K2.u9927 from rfl, allE_node, arows9924, irow9928, arows9927]
  all_goals rfl

theorem atot9928 : totK PD2M8K2 D2M8K2.u9928 = [0, 0, 898581391669, 3079398519549, 2682999000403, 432178465650, 14256699425, 0] := by
  rw [show D2M8K2.u9928 = KTree.node D2M8K2.u9924 (nat_lit 21161420) (nat_lit 3300260735) (nat_lit 0) D2M8K2.u9927 from rfl, totK_node, atot9924, atot9927]
  decide +kernel

theorem arows9936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9936 = true := by
  rw [show D2M8K2.u9936 = KTree.node D2M8K2.u9932 (nat_lit 21168424) (nat_lit 2736765683) (nat_lit 520) D2M8K2.u9935 from rfl, allE_node, arows9932, irow9936, arows9935]
  all_goals rfl

theorem atot9936 : totK PD2M8K2 D2M8K2.u9936 = [0, 0, 737384741921, 2854707581289, 2896791125970, 574295083199, 20157898232, 0] := by
  rw [show D2M8K2.u9936 = KTree.node D2M8K2.u9932 (nat_lit 21168424) (nat_lit 2736765683) (nat_lit 520) D2M8K2.u9935 from rfl, totK_node, atot9932, atot9935]
  decide +kernel

theorem arows9943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9943 = true := by
  rw [show D2M8K2.u9943 = KTree.node D2M8K2.u9939 (nat_lit 21179589) (nat_lit 1515656845) (nat_lit 0) D2M8K2.u9942 from rfl, allE_node, arows9939, irow9943, arows9942]
  all_goals rfl

theorem atot9943 : totK PD2M8K2 D2M8K2.u9943 = [0, 0, 0, 1396260991934, 3660127460336, 1728896537314, 157536140430, 1369150432] := by
  rw [show D2M8K2.u9943 = KTree.node D2M8K2.u9939 (nat_lit 21179589) (nat_lit 1515656845) (nat_lit 0) D2M8K2.u9942 from rfl, totK_node, atot9939, atot9942]
  decide +kernel

theorem arows9952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9952 = true := by
  rw [show D2M8K2.u9952 = KTree.node D2M8K2.u9948 (nat_lit 21235134) (nat_lit 2349543212) (nat_lit 8) D2M8K2.u9951 from rfl, allE_node, arows9948, irow9952, arows9951]
  all_goals rfl

theorem atot9952 : totK PD2M8K2 D2M8K2.u9952 = [0, 0, 841209018313, 2998949011354, 2769709653412, 524277067751, 19466032994, 0] := by
  rw [show D2M8K2.u9952 = KTree.node D2M8K2.u9948 (nat_lit 21235134) (nat_lit 2349543212) (nat_lit 8) D2M8K2.u9951 from rfl, totK_node, atot9948, atot9951]
  decide +kernel

theorem arows9959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9959 = true := by
  rw [show D2M8K2.u9959 = KTree.node D2M8K2.u9955 (nat_lit 21249564) (nat_lit 2485769076) (nat_lit 0) D2M8K2.u9958 from rfl, allE_node, arows9955, irow9959, arows9958]
  all_goals rfl

theorem atot9959 : totK PD2M8K2 D2M8K2.u9959 = [0, 0, 1046307499060, 3349167523362, 2502004948966, 266244285697, 2260824724, 0] := by
  rw [show D2M8K2.u9959 = KTree.node D2M8K2.u9955 (nat_lit 21249564) (nat_lit 2485769076) (nat_lit 0) D2M8K2.u9958 from rfl, totK_node, atot9955, atot9958]
  decide +kernel

theorem arows9967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9967 = true := by
  rw [show D2M8K2.u9967 = KTree.node D2M8K2.u9963 (nat_lit 21280043) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u9966 from rfl, allE_node, arows9963, irow9967, arows9966]
  all_goals rfl

theorem atot9967 : totK PD2M8K2 D2M8K2.u9967 = [0, 0, 953358695789, 3205341251553, 2695020642465, 409584543888, 6717958024, 0] := by
  rw [show D2M8K2.u9967 = KTree.node D2M8K2.u9963 (nat_lit 21280043) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u9966 from rfl, totK_node, atot9963, atot9966]
  decide +kernel

theorem arows9974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9974 = true := by
  rw [show D2M8K2.u9974 = KTree.node D2M8K2.u9970 (nat_lit 21290205) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u9973 from rfl, allE_node, arows9970, irow9974, arows9973]
  all_goals rfl

theorem atot9974 : totK PD2M8K2 D2M8K2.u9974 = [0, 0, 820647186885, 2956223345012, 2842219198933, 538572573927, 18088360733, 0] := by
  rw [show D2M8K2.u9974 = KTree.node D2M8K2.u9970 (nat_lit 21290205) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u9973 from rfl, totK_node, atot9970, atot9973]
  decide +kernel

theorem arows9986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9986 = true := by
  rw [show D2M8K2.u9986 = KTree.node D2M8K2.u9982 (nat_lit 21318346) (nat_lit 3871581885) (nat_lit 0) D2M8K2.u9985 from rfl, allE_node, arows9982, irow9986, arows9985]
  all_goals rfl

theorem atot9986 : totK PD2M8K2 D2M8K2.u9986 = [0, 0, 743198313688, 3022113609465, 2886747919148, 498021275073, 15083816312, 0] := by
  rw [show D2M8K2.u9986 = KTree.node D2M8K2.u9982 (nat_lit 21318346) (nat_lit 3871581885) (nat_lit 0) D2M8K2.u9985 from rfl, totK_node, atot9982, atot9985]
  decide +kernel

theorem arows9993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9993 = true := by
  rw [show D2M8K2.u9993 = KTree.node D2M8K2.u9989 (nat_lit 21327380) (nat_lit 3665666850) (nat_lit 0) D2M8K2.u9992 from rfl, allE_node, arows9989, irow9993, arows9992]
  all_goals rfl

theorem atot9993 : totK PD2M8K2 D2M8K2.u9993 = [0, 0, 931564585830, 3076915527783, 2656199463396, 452831545920, 15758197833, 0] := by
  rw [show D2M8K2.u9993 = KTree.node D2M8K2.u9989 (nat_lit 21327380) (nat_lit 3665666850) (nat_lit 0) D2M8K2.u9992 from rfl, totK_node, atot9989, atot9992]
  decide +kernel

theorem arows10001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10001 = true := by
  rw [show D2M8K2.u10001 = KTree.node D2M8K2.u9997 (nat_lit 21358764) (nat_lit 3122618704) (nat_lit 0) D2M8K2.u10000 from rfl, allE_node, arows9997, irow10001, arows10000]
  all_goals rfl

theorem atot10001 : totK PD2M8K2 D2M8K2.u10001 = [0, 0, 894060434593, 3141449069228, 2746790412056, 400103560719, 6349665391, 0] := by
  rw [show D2M8K2.u10001 = KTree.node D2M8K2.u9997 (nat_lit 21358764) (nat_lit 3122618704) (nat_lit 0) D2M8K2.u10000 from rfl, totK_node, atot9997, atot10000]
  decide +kernel

theorem arows10008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10008 = true := by
  rw [show D2M8K2.u10008 = KTree.node D2M8K2.u10004 (nat_lit 21369424) (nat_lit 1686180725) (nat_lit 0) D2M8K2.u10007 from rfl, allE_node, arows10004, irow10008, arows10007]
  all_goals rfl

theorem atot10008 : totK PD2M8K2 D2M8K2.u10008 = [0, 0, 1198846358480, 3429652560149, 2362718528455, 309979715838, 5193381917, 0] := by
  rw [show D2M8K2.u10008 = KTree.node D2M8K2.u10004 (nat_lit 21369424) (nat_lit 1686180725) (nat_lit 0) D2M8K2.u10007 from rfl, totK_node, atot10004, atot10007]
  decide +kernel

theorem arows10017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10017 = true := by
  rw [show D2M8K2.u10017 = KTree.node D2M8K2.u10013 (nat_lit 21445383) (nat_lit 3629924412) (nat_lit 0) D2M8K2.u10016 from rfl, allE_node, arows10013, irow10017, arows10016]
  all_goals rfl

theorem atot10017 : totK PD2M8K2 D2M8K2.u10017 = [0, 500771732234, 1908682536316, 2751422338097, 1783879690041, 342839354983, 13930390162, 0] := by
  rw [show D2M8K2.u10017 = KTree.node D2M8K2.u10013 (nat_lit 21445383) (nat_lit 3629924412) (nat_lit 0) D2M8K2.u10016 from rfl, totK_node, atot10013, atot10016]
  decide +kernel

theorem arows10024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10024 = true := by
  rw [show D2M8K2.u10024 = KTree.node D2M8K2.u10020 (nat_lit 21451637) (nat_lit 1864847234) (nat_lit 0) D2M8K2.u10023 from rfl, allE_node, arows10020, irow10024, arows10023]
  all_goals rfl

theorem atot10024 : totK PD2M8K2 D2M8K2.u10024 = [0, 823398881554, 2887339843421, 2853546051529, 643022978658, 22282010923, 0, 0] := by
  rw [show D2M8K2.u10024 = KTree.node D2M8K2.u10020 (nat_lit 21451637) (nat_lit 1864847234) (nat_lit 0) D2M8K2.u10023 from rfl, totK_node, atot10020, atot10023]
  decide +kernel

theorem arows10032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10032 = true := by
  rw [show D2M8K2.u10032 = KTree.node D2M8K2.u10028 (nat_lit 21458520) (nat_lit 3316160414) (nat_lit 0) D2M8K2.u10031 from rfl, allE_node, arows10028, irow10032, arows10031]
  all_goals rfl

theorem atot10032 : totK PD2M8K2 D2M8K2.u10032 = [0, 793563709804, 2923903784410, 2886434817251, 608114265099, 12487235341, 0, 0] := by
  rw [show D2M8K2.u10032 = KTree.node D2M8K2.u10028 (nat_lit 21458520) (nat_lit 3316160414) (nat_lit 0) D2M8K2.u10031 from rfl, totK_node, atot10028, atot10031]
  decide +kernel

theorem arows10039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10039 = true := by
  rw [show D2M8K2.u10039 = KTree.node D2M8K2.u10035 (nat_lit 21468060) (nat_lit 1400421485) (nat_lit 0) D2M8K2.u10038 from rfl, allE_node, arows10035, irow10039, arows10038]
  all_goals rfl

theorem atot10039 : totK PD2M8K2 D2M8K2.u10039 = [0, 0, 850162529424, 2884437889988, 2758719430088, 735826859643, 40931783143, 0] := by
  rw [show D2M8K2.u10039 = KTree.node D2M8K2.u10035 (nat_lit 21468060) (nat_lit 1400421485) (nat_lit 0) D2M8K2.u10038 from rfl, totK_node, atot10035, atot10038]
  decide +kernel

theorem arows10049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10049 = true := by
  rw [show D2M8K2.u10049 = KTree.node D2M8K2.u10045 (nat_lit 21475061) (nat_lit 2293565314) (nat_lit 0) D2M8K2.u10048 from rfl, allE_node, arows10045, irow10049, arows10048]
  all_goals rfl

theorem atot10049 : totK PD2M8K2 D2M8K2.u10049 = [0, 0, 837418864508, 3109021822406, 2820390219127, 439352181699, 6368832031, 0] := by
  rw [show D2M8K2.u10049 = KTree.node D2M8K2.u10045 (nat_lit 21475061) (nat_lit 2293565314) (nat_lit 0) D2M8K2.u10048 from rfl, totK_node, atot10045, atot10048]
  decide +kernel

theorem arows10056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10056 = true := by
  rw [show D2M8K2.u10056 = KTree.node D2M8K2.u10052 (nat_lit 21482328) (nat_lit 3435439241) (nat_lit 0) D2M8K2.u10055 from rfl, allE_node, arows10052, irow10056, arows10055]
  all_goals rfl

theorem atot10056 : totK PD2M8K2 D2M8K2.u10056 = [0, 429522638084, 1781758022183, 2744781618558, 1904900605911, 402555353537, 10717512769, 0] := by
  rw [show D2M8K2.u10056 = KTree.node D2M8K2.u10052 (nat_lit 21482328) (nat_lit 3435439241) (nat_lit 0) D2M8K2.u10055 from rfl, totK_node, atot10052, atot10055]
  decide +kernel

theorem arows10064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10064 = true := by
  rw [show D2M8K2.u10064 = KTree.node D2M8K2.u10060 (nat_lit 21491782) (nat_lit 3728482711) (nat_lit 0) D2M8K2.u10063 from rfl, allE_node, arows10060, irow10064, arows10063]
  all_goals rfl

theorem atot10064 : totK PD2M8K2 D2M8K2.u10064 = [0, 826728102901, 2970414015805, 2809531268443, 612231498377, 21239436005, 0, 0] := by
  rw [show D2M8K2.u10064 = KTree.node D2M8K2.u10060 (nat_lit 21491782) (nat_lit 3728482711) (nat_lit 0) D2M8K2.u10063 from rfl, totK_node, atot10060, atot10063]
  decide +kernel

theorem arows10071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10071 = true := by
  rw [show D2M8K2.u10071 = KTree.node D2M8K2.u10067 (nat_lit 21502400) (nat_lit 3118497019) (nat_lit 0) D2M8K2.u10070 from rfl, allE_node, arows10067, irow10071, arows10070]
  all_goals rfl

theorem atot10071 : totK PD2M8K2 D2M8K2.u10071 = [0, 405776974296, 2170285655220, 3317233742025, 1298451791448, 80644129946, 0, 0] := by
  rw [show D2M8K2.u10071 = KTree.node D2M8K2.u10067 (nat_lit 21502400) (nat_lit 3118497019) (nat_lit 0) D2M8K2.u10070 from rfl, totK_node, atot10067, atot10070]
  decide +kernel

theorem arows10080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10080 = true := by
  rw [show D2M8K2.u10080 = KTree.node D2M8K2.u10076 (nat_lit 21517742) (nat_lit 3801943950) (nat_lit 0) D2M8K2.u10079 from rfl, allE_node, arows10076, irow10080, arows10079]
  all_goals rfl

theorem atot10080 : totK PD2M8K2 D2M8K2.u10080 = [0, 0, 977032785616, 3269665513406, 2521084858872, 359394169620, 7048116272, 0] := by
  rw [show D2M8K2.u10080 = KTree.node D2M8K2.u10076 (nat_lit 21517742) (nat_lit 3801943950) (nat_lit 0) D2M8K2.u10079 from rfl, totK_node, atot10076, atot10079]
  decide +kernel

theorem arows10087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10087 = true := by
  rw [show D2M8K2.u10087 = KTree.node D2M8K2.u10083 (nat_lit 21527947) (nat_lit 1742990493) (nat_lit 0) D2M8K2.u10086 from rfl, allE_node, arows10083, irow10087, arows10086]
  all_goals rfl

theorem atot10087 : totK PD2M8K2 D2M8K2.u10087 = [0, 772198506418, 2819291795452, 2851873100762, 800730302728, 45717124287, 0, 0] := by
  rw [show D2M8K2.u10087 = KTree.node D2M8K2.u10083 (nat_lit 21527947) (nat_lit 1742990493) (nat_lit 0) D2M8K2.u10086 from rfl, totK_node, atot10083, atot10086]
  decide +kernel

theorem arows10095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10095 = true := by
  rw [show D2M8K2.u10095 = KTree.node D2M8K2.u10091 (nat_lit 21537273) (nat_lit 1840888922) (nat_lit 0) D2M8K2.u10094 from rfl, allE_node, arows10091, irow10095, arows10094]
  all_goals rfl

theorem atot10095 : totK PD2M8K2 D2M8K2.u10095 = [0, 853379733753, 2975167407530, 2808177273010, 598896081752, 21146926224, 0, 0] := by
  rw [show D2M8K2.u10095 = KTree.node D2M8K2.u10091 (nat_lit 21537273) (nat_lit 1840888922) (nat_lit 0) D2M8K2.u10094 from rfl, totK_node, atot10091, atot10094]
  decide +kernel

theorem arows10102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10102 = true := by
  rw [show D2M8K2.u10102 = KTree.node D2M8K2.u10098 (nat_lit 21543967) (nat_lit 2362202289) (nat_lit 0) D2M8K2.u10101 from rfl, allE_node, arows10098, irow10102, arows10101]
  all_goals rfl

theorem atot10102 : totK PD2M8K2 D2M8K2.u10102 = [0, 417183842111, 1994103390899, 3113473081735, 1515661046038, 148608125980, 1239866073, 0] := by
  rw [show D2M8K2.u10102 = KTree.node D2M8K2.u10098 (nat_lit 21543967) (nat_lit 2362202289) (nat_lit 0) D2M8K2.u10101 from rfl, totK_node, atot10098, atot10101]
  decide +kernel

theorem arows10113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10113 = true := by
  rw [show D2M8K2.u10113 = KTree.node D2M8K2.u10109 (nat_lit 21556540) (nat_lit 3574133751) (nat_lit 0) D2M8K2.u10112 from rfl, allE_node, arows10109, irow10113, arows10112]
  all_goals rfl

theorem atot10113 : totK PD2M8K2 D2M8K2.u10113 = [0, 0, 1112911278325, 3325219388509, 2361472489641, 381009309181, 13105450397, 0] := by
  rw [show D2M8K2.u10113 = KTree.node D2M8K2.u10109 (nat_lit 21556540) (nat_lit 3574133751) (nat_lit 0) D2M8K2.u10112 from rfl, totK_node, atot10109, atot10112]
  decide +kernel

theorem arows10120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10120 = true := by
  rw [show D2M8K2.u10120 = KTree.node D2M8K2.u10116 (nat_lit 21563600) (nat_lit 2890220354) (nat_lit 0) D2M8K2.u10119 from rfl, allE_node, arows10116, irow10120, arows10119]
  all_goals rfl

theorem atot10120 : totK PD2M8K2 D2M8K2.u10120 = [0, 502750546267, 2070816134637, 2864639235760, 1516063466945, 203075778833, 4720618446, 0] := by
  rw [show D2M8K2.u10120 = KTree.node D2M8K2.u10116 (nat_lit 21563600) (nat_lit 2890220354) (nat_lit 0) D2M8K2.u10119 from rfl, totK_node, atot10116, atot10119]
  decide +kernel

theorem arows10128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10128 = true := by
  rw [show D2M8K2.u10128 = KTree.node D2M8K2.u10124 (nat_lit 21572549) (nat_lit 2343662941) (nat_lit 0) D2M8K2.u10127 from rfl, allE_node, arows10124, irow10128, arows10127]
  all_goals rfl

theorem atot10128 : totK PD2M8K2 D2M8K2.u10128 = [0, 781909777871, 2738037966906, 2814171354312, 853834555771, 49487115836, 0, 0] := by
  rw [show D2M8K2.u10128 = KTree.node D2M8K2.u10124 (nat_lit 21572549) (nat_lit 2343662941) (nat_lit 0) D2M8K2.u10127 from rfl, totK_node, atot10124, atot10127]
  decide +kernel

theorem arows10135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10135 = true := by
  rw [show D2M8K2.u10135 = KTree.node D2M8K2.u10131 (nat_lit 21579602) (nat_lit 4112515687) (nat_lit 0) D2M8K2.u10134 from rfl, allE_node, arows10131, irow10135, arows10134]
  all_goals rfl

theorem atot10135 : totK PD2M8K2 D2M8K2.u10135 = [0, 702824139145, 2829540273262, 2992987600161, 669377683234, 19601020673, 0, 0] := by
  rw [show D2M8K2.u10135 = KTree.node D2M8K2.u10131 (nat_lit 21579602) (nat_lit 4112515687) (nat_lit 0) D2M8K2.u10134 from rfl, totK_node, atot10131, atot10134]
  decide +kernel

theorem arows10144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10144 = true := by
  rw [show D2M8K2.u10144 = KTree.node D2M8K2.u10140 (nat_lit 21593433) (nat_lit 1829234082) (nat_lit 0) D2M8K2.u10143 from rfl, allE_node, arows10140, irow10144, arows10143]
  all_goals rfl

theorem atot10144 : totK PD2M8K2 D2M8K2.u10144 = [0, 0, 1499402400095, 3781226363256, 1826202475247, 113999410219, 0, 0] := by
  rw [show D2M8K2.u10144 = KTree.node D2M8K2.u10140 (nat_lit 21593433) (nat_lit 1829234082) (nat_lit 0) D2M8K2.u10143 from rfl, totK_node, atot10140, atot10143]
  decide +kernel

theorem arows10151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10151 = true := by
  rw [show D2M8K2.u10151 = KTree.node D2M8K2.u10147 (nat_lit 21607037) (nat_lit 2283722222) (nat_lit 0) D2M8K2.u10150 from rfl, allE_node, arows10147, irow10151, arows10150]
  all_goals rfl

theorem atot10151 : totK PD2M8K2 D2M8K2.u10151 = [0, 593742132755, 2147575070754, 2778126071304, 1429062705015, 225001327227, 4977114383, 0] := by
  rw [show D2M8K2.u10151 = KTree.node D2M8K2.u10147 (nat_lit 21607037) (nat_lit 2283722222) (nat_lit 0) D2M8K2.u10150 from rfl, totK_node, atot10147, atot10150]
  decide +kernel

theorem arows10159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10159 = true := by
  rw [show D2M8K2.u10159 = KTree.node D2M8K2.u10155 (nat_lit 21614250) (nat_lit 3567621219) (nat_lit 0) D2M8K2.u10158 from rfl, allE_node, arows10155, irow10159, arows10158]
  all_goals rfl

theorem atot10159 : totK PD2M8K2 D2M8K2.u10159 = [0, 715179611310, 2708023443471, 2928967371911, 883247545762, 47070066425, 0, 0] := by
  rw [show D2M8K2.u10159 = KTree.node D2M8K2.u10155 (nat_lit 21614250) (nat_lit 3567621219) (nat_lit 0) D2M8K2.u10158 from rfl, totK_node, atot10155, atot10158]
  decide +kernel

theorem arows10166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10166 = true := by
  rw [show D2M8K2.u10166 = KTree.node D2M8K2.u10162 (nat_lit 21624676) (nat_lit 4003814300) (nat_lit 0) D2M8K2.u10165 from rfl, allE_node, arows10162, irow10166, arows10165]
  all_goals rfl

theorem atot10166 : totK PD2M8K2 D2M8K2.u10166 = [0, 690416030819, 2716326263469, 3001071358810, 788739468253, 35257682112, 0, 0] := by
  rw [show D2M8K2.u10166 = KTree.node D2M8K2.u10162 (nat_lit 21624676) (nat_lit 4003814300) (nat_lit 0) D2M8K2.u10165 from rfl, totK_node, atot10162, atot10165]
  decide +kernel

theorem arows10176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10176 = true := by
  rw [show D2M8K2.u10176 = KTree.node D2M8K2.u10172 (nat_lit 21632144) (nat_lit 3577771489) (nat_lit 0) D2M8K2.u10175 from rfl, allE_node, arows10172, irow10176, arows10175]
  all_goals rfl

theorem atot10176 : totK PD2M8K2 D2M8K2.u10176 = [0, 0, 1066932669058, 3402538797497, 2500047131042, 289127374014, 2745449626, 0] := by
  rw [show D2M8K2.u10176 = KTree.node D2M8K2.u10172 (nat_lit 21632144) (nat_lit 3577771489) (nat_lit 0) D2M8K2.u10175 from rfl, totK_node, atot10172, atot10175]
  decide +kernel

theorem arows10183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10183 = true := by
  rw [show D2M8K2.u10183 = KTree.node D2M8K2.u10179 (nat_lit 21641306) (nat_lit 4014886107) (nat_lit 0) D2M8K2.u10182 from rfl, allE_node, arows10179, irow10183, arows10182]
  all_goals rfl

theorem atot10183 : totK PD2M8K2 D2M8K2.u10183 = [0, 0, 854863914192, 3052690104795, 2764624811893, 500866007292, 11122171587, 0] := by
  rw [show D2M8K2.u10183 = KTree.node D2M8K2.u10179 (nat_lit 21641306) (nat_lit 4014886107) (nat_lit 0) D2M8K2.u10182 from rfl, totK_node, atot10179, atot10182]
  decide +kernel

theorem arows10191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10191 = true := by
  rw [show D2M8K2.u10191 = KTree.node D2M8K2.u10187 (nat_lit 22397870) (nat_lit 3282498671) (nat_lit 0) D2M8K2.u10190 from rfl, allE_node, arows10187, irow10191, arows10190]
  all_goals rfl

theorem atot10191 : totK PD2M8K2 D2M8K2.u10191 = [0, 918134824901, 3045255120130, 2502305737922, 564145928287, 133480950375, 11893557120, 0] := by
  rw [show D2M8K2.u10191 = KTree.node D2M8K2.u10187 (nat_lit 22397870) (nat_lit 3282498671) (nat_lit 0) D2M8K2.u10190 from rfl, totK_node, atot10187, atot10190]
  decide +kernel

theorem arows10198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10198 = true := by
  rw [show D2M8K2.u10198 = KTree.node D2M8K2.u10194 (nat_lit 22409067) (nat_lit 3663254416) (nat_lit 0) D2M8K2.u10197 from rfl, allE_node, arows10194, irow10198, arows10197]
  all_goals rfl

theorem atot10198 : totK PD2M8K2 D2M8K2.u10198 = [0, 831183571984, 2946302656742, 2796612556989, 579082354112, 18231200220, 0, 0] := by
  rw [show D2M8K2.u10198 = KTree.node D2M8K2.u10194 (nat_lit 22409067) (nat_lit 3663254416) (nat_lit 0) D2M8K2.u10197 from rfl, totK_node, atot10194, atot10197]
  decide +kernel

theorem arows10207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10207 = true := by
  rw [show D2M8K2.u10207 = KTree.node D2M8K2.u10203 (nat_lit 22415880) (nat_lit 3609730544) (nat_lit 0) D2M8K2.u10206 from rfl, allE_node, arows10203, irow10207, arows10206]
  all_goals rfl

theorem atot10207 : totK PD2M8K2 D2M8K2.u10207 = [0, 256489885996, 1696501967774, 3274718751281, 1662419994063, 164067659689, 1369150432, 0] := by
  rw [show D2M8K2.u10207 = KTree.node D2M8K2.u10203 (nat_lit 22415880) (nat_lit 3609730544) (nat_lit 0) D2M8K2.u10206 from rfl, totK_node, atot10203, atot10206]
  decide +kernel

theorem arows10214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10214 = true := by
  rw [show D2M8K2.u10214 = KTree.node D2M8K2.u10210 (nat_lit 22429986) (nat_lit 2953524173) (nat_lit 0) D2M8K2.u10213 from rfl, allE_node, arows10210, irow10214, arows10213]
  all_goals rfl

theorem atot10214 : totK PD2M8K2 D2M8K2.u10214 = [0, 94308289763, 1597633133113, 3708332735241, 1670753405391, 77055550360, 0, 0] := by
  rw [show D2M8K2.u10214 = KTree.node D2M8K2.u10210 (nat_lit 22429986) (nat_lit 2953524173) (nat_lit 0) D2M8K2.u10213 from rfl, totK_node, atot10210, atot10213]
  decide +kernel

theorem arows10222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10222 = true := by
  rw [show D2M8K2.u10222 = KTree.node D2M8K2.u10218 (nat_lit 22443003) (nat_lit 3764946393) (nat_lit 0) D2M8K2.u10221 from rfl, allE_node, arows10218, irow10222, arows10221]
  all_goals rfl

theorem atot10222 : totK PD2M8K2 D2M8K2.u10222 = [0, 777449597220, 2789164240458, 2880826556726, 828514399487, 44519461602, 0, 0] := by
  rw [show D2M8K2.u10222 = KTree.node D2M8K2.u10218 (nat_lit 22443003) (nat_lit 3764946393) (nat_lit 0) D2M8K2.u10221 from rfl, totK_node, atot10218, atot10221]
  decide +kernel

theorem arows10229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10229 = true := by
  rw [show D2M8K2.u10229 = KTree.node D2M8K2.u10225 (nat_lit 22450338) (nat_lit 2806703644) (nat_lit 0) D2M8K2.u10228 from rfl, allE_node, arows10225, irow10229, arows10228]
  all_goals rfl

theorem atot10229 : totK PD2M8K2 D2M8K2.u10229 = [0, 835009255261, 2977376847281, 2833105015987, 582320287905, 18214542822, 0, 0] := by
  rw [show D2M8K2.u10229 = KTree.node D2M8K2.u10225 (nat_lit 22450338) (nat_lit 2806703644) (nat_lit 0) D2M8K2.u10228 from rfl, totK_node, atot10225, atot10228]
  decide +kernel

theorem arows10244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10244 = true := by
  rw [show D2M8K2.u10244 = KTree.node D2M8K2.u10240 (nat_lit 22460891) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u10243 from rfl, allE_node, arows10240, irow10244, arows10243]
  all_goals rfl

theorem atot10244 : totK PD2M8K2 D2M8K2.u10244 = [0, 318671753230, 1718699395163, 2966212108976, 1842040133477, 403093805720, 24064559466, 0] := by
  rw [show D2M8K2.u10244 = KTree.node D2M8K2.u10240 (nat_lit 22460891) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u10243 from rfl, totK_node, atot10240, atot10243]
  decide +kernel

theorem arows10251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10251 = true := by
  rw [show D2M8K2.u10251 = KTree.node D2M8K2.u10247 (nat_lit 22467842) (nat_lit 4107459482) (nat_lit 0) D2M8K2.u10250 from rfl, allE_node, arows10247, irow10251, arows10250]
  all_goals rfl

theorem atot10251 : totK PD2M8K2 D2M8K2.u10251 = [0, 0, 909266272332, 3063606250868, 2720521931997, 535793482857, 12874606741, 0] := by
  rw [show D2M8K2.u10251 = KTree.node D2M8K2.u10247 (nat_lit 22467842) (nat_lit 4107459482) (nat_lit 0) D2M8K2.u10250 from rfl, totK_node, atot10247, atot10250]
  decide +kernel

theorem arows10259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10259 = true := by
  rw [show D2M8K2.u10259 = KTree.node D2M8K2.u10255 (nat_lit 22475000) (nat_lit 2850981948) (nat_lit 0) D2M8K2.u10258 from rfl, allE_node, arows10255, irow10259, arows10258]
  all_goals rfl

theorem atot10259 : totK PD2M8K2 D2M8K2.u10259 = [0, 241137231530, 1182963233062, 2802628012745, 2538070329396, 446199332228, 8087477235, 0] := by
  rw [show D2M8K2.u10259 = KTree.node D2M8K2.u10255 (nat_lit 22475000) (nat_lit 2850981948) (nat_lit 0) D2M8K2.u10258 from rfl, totK_node, atot10255, atot10258]
  decide +kernel

theorem arows10266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10266 = true := by
  rw [show D2M8K2.u10266 = KTree.node D2M8K2.u10262 (nat_lit 22523869) (nat_lit 995820213) (nat_lit 0) D2M8K2.u10265 from rfl, allE_node, arows10262, irow10266, arows10265]
  all_goals rfl

theorem atot10266 : totK PD2M8K2 D2M8K2.u10266 = [0, 778755885752, 2836752105596, 2859240362850, 762060409529, 36520588978, 0, 0] := by
  rw [show D2M8K2.u10266 = KTree.node D2M8K2.u10262 (nat_lit 22523869) (nat_lit 995820213) (nat_lit 0) D2M8K2.u10265 from rfl, totK_node, atot10262, atot10265]
  decide +kernel

theorem arows10275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10275 = true := by
  rw [show D2M8K2.u10275 = KTree.node D2M8K2.u10271 (nat_lit 22533343) (nat_lit 2383192834) (nat_lit 0) D2M8K2.u10274 from rfl, allE_node, arows10271, irow10275, arows10274]
  all_goals rfl

theorem atot10275 : totK PD2M8K2 D2M8K2.u10275 = [0, 794378507650, 2943379309191, 2891069694380, 593180933502, 18231200220, 0, 0] := by
  rw [show D2M8K2.u10275 = KTree.node D2M8K2.u10271 (nat_lit 22533343) (nat_lit 2383192834) (nat_lit 0) D2M8K2.u10274 from rfl, totK_node, atot10271, atot10274]
  decide +kernel

theorem arows10282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10282 = true := by
  rw [show D2M8K2.u10282 = KTree.node D2M8K2.u10278 (nat_lit 22540090) (nat_lit 3821490449) (nat_lit 0) D2M8K2.u10281 from rfl, allE_node, arows10278, irow10282, arows10281]
  all_goals rfl

theorem atot10282 : totK PD2M8K2 D2M8K2.u10282 = [0, 319054120400, 1789886710590, 3184348539557, 1698044188156, 164936841360, 1239866073, 0] := by
  rw [show D2M8K2.u10282 = KTree.node D2M8K2.u10278 (nat_lit 22540090) (nat_lit 3821490449) (nat_lit 0) D2M8K2.u10281 from rfl, totK_node, atot10278, atot10281]
  decide +kernel

theorem arows10290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10290 = true := by
  rw [show D2M8K2.u10290 = KTree.node D2M8K2.u10286 (nat_lit 22551992) (nat_lit 2463599069) (nat_lit 0) D2M8K2.u10289 from rfl, allE_node, arows10286, irow10290, arows10289]
  all_goals rfl

theorem atot10290 : totK PD2M8K2 D2M8K2.u10290 = [0, 0, 1170419369232, 3358657254767, 2282793837297, 365397652844, 13105450397, 0] := by
  rw [show D2M8K2.u10290 = KTree.node D2M8K2.u10286 (nat_lit 22551992) (nat_lit 2463599069) (nat_lit 0) D2M8K2.u10289 from rfl, totK_node, atot10286, atot10289]
  decide +kernel

theorem arows10297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10297 = true := by
  rw [show D2M8K2.u10297 = KTree.node D2M8K2.u10293 (nat_lit 22558982) (nat_lit 2608622746) (nat_lit 0) D2M8K2.u10296 from rfl, allE_node, arows10293, irow10297, arows10296]
  all_goals rfl

theorem atot10297 : totK PD2M8K2 D2M8K2.u10297 = [0, 499131794211, 2030363932493, 2850304598832, 1517681401929, 205559689487, 4720618446, 0] := by
  rw [show D2M8K2.u10297 = KTree.node D2M8K2.u10293 (nat_lit 22558982) (nat_lit 2608622746) (nat_lit 0) D2M8K2.u10296 from rfl, totK_node, atot10293, atot10296]
  decide +kernel

theorem arows10307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10307 = true := by
  rw [show D2M8K2.u10307 = KTree.node D2M8K2.u10303 (nat_lit 22567454) (nat_lit 3881137344) (nat_lit 0) D2M8K2.u10306 from rfl, allE_node, arows10303, irow10307, arows10306]
  all_goals rfl

theorem atot10307 : totK PD2M8K2 D2M8K2.u10307 = [0, 821208412223, 2821736489708, 2756998053040, 779889819209, 40529482973, 0, 0] := by
  rw [show D2M8K2.u10307 = KTree.node D2M8K2.u10303 (nat_lit 22567454) (nat_lit 3881137344) (nat_lit 0) D2M8K2.u10306 from rfl, totK_node, atot10303, atot10306]
  decide +kernel

theorem arows10314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10314 = true := by
  rw [show D2M8K2.u10314 = KTree.node D2M8K2.u10310 (nat_lit 22574927) (nat_lit 2087254791) (nat_lit 0) D2M8K2.u10313 from rfl, allE_node, arows10310, irow10314, arows10313]
  all_goals rfl

theorem atot10314 : totK PD2M8K2 D2M8K2.u10314 = [0, 691322795816, 2819715254581, 3025656766000, 675636167929, 19601020673, 0, 0] := by
  rw [show D2M8K2.u10314 = KTree.node D2M8K2.u10310 (nat_lit 22574927) (nat_lit 2087254791) (nat_lit 0) D2M8K2.u10313 from rfl, totK_node, atot10310, atot10313]
  decide +kernel

theorem arows10322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10322 = true := by
  rw [show D2M8K2.u10322 = KTree.node D2M8K2.u10318 (nat_lit 22585924) (nat_lit 2975969487) (nat_lit 0) D2M8K2.u10321 from rfl, allE_node, arows10318, irow10322, arows10321]
  all_goals rfl

theorem atot10322 : totK PD2M8K2 D2M8K2.u10322 = [0, 0, 1304387183848, 3633559960520, 2009015457571, 160222635703, 1138244013, 0] := by
  rw [show D2M8K2.u10322 = KTree.node D2M8K2.u10318 (nat_lit 22585924) (nat_lit 2975969487) (nat_lit 0) D2M8K2.u10321 from rfl, totK_node, atot10318, atot10321]
  decide +kernel

theorem arows10329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10329 = true := by
  rw [show D2M8K2.u10329 = KTree.node D2M8K2.u10325 (nat_lit 22597445) (nat_lit 2270366297) (nat_lit 0) D2M8K2.u10328 from rfl, allE_node, arows10325, irow10329, arows10328]
  all_goals rfl

theorem atot10329 : totK PD2M8K2 D2M8K2.u10329 = [0, 407653508827, 1844210105820, 2947409857573, 1666756014109, 221148441833, 4977114383, 0] := by
  rw [show D2M8K2.u10329 = KTree.node D2M8K2.u10325 (nat_lit 22597445) (nat_lit 2270366297) (nat_lit 0) D2M8K2.u10328 from rfl, totK_node, atot10325, atot10328]
  decide +kernel

theorem arows10338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10338 = true := by
  rw [show D2M8K2.u10338 = KTree.node D2M8K2.u10334 (nat_lit 22608321) (nat_lit 1763671237) (nat_lit 0) D2M8K2.u10337 from rfl, allE_node, arows10334, irow10338, arows10337]
  all_goals rfl

theorem atot10338 : totK PD2M8K2 D2M8K2.u10338 = [0, 745720552880, 2769408146584, 2927735943403, 803415173039, 38326445845, 0, 0] := by
  rw [show D2M8K2.u10338 = KTree.node D2M8K2.u10334 (nat_lit 22608321) (nat_lit 1763671237) (nat_lit 0) D2M8K2.u10337 from rfl, totK_node, atot10334, atot10337]
  decide +kernel

theorem arows10345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10345 = true := by
  rw [show D2M8K2.u10345 = KTree.node D2M8K2.u10341 (nat_lit 22615566) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u10344 from rfl, allE_node, arows10341, irow10345, arows10344]
  all_goals rfl

theorem atot10345 : totK PD2M8K2 D2M8K2.u10345 = [0, 869024644006, 3000605200879, 2798070982619, 594504356756, 18637176562, 0, 0] := by
  rw [show D2M8K2.u10345 = KTree.node D2M8K2.u10341 (nat_lit 22615566) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u10344 from rfl, totK_node, atot10341, atot10344]
  decide +kernel

theorem arows10353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10353 = true := by
  rw [show D2M8K2.u10353 = KTree.node D2M8K2.u10349 (nat_lit 22625659) (nat_lit 1717789724) (nat_lit 0) D2M8K2.u10352 from rfl, allE_node, arows10349, irow10353, arows10352]
  all_goals rfl

theorem atot10353 : totK PD2M8K2 D2M8K2.u10353 = [0, 0, 1242236520298, 3526892407206, 2216110836954, 203413314758, 1310285577, 0] := by
  rw [show D2M8K2.u10353 = KTree.node D2M8K2.u10349 (nat_lit 22625659) (nat_lit 1717789724) (nat_lit 0) D2M8K2.u10352 from rfl, totK_node, atot10349, atot10352]
  decide +kernel

theorem arows10360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10360 = true := by
  rw [show D2M8K2.u10360 = KTree.node D2M8K2.u10356 (nat_lit 22635082) (nat_lit 3897284932) (nat_lit 0) D2M8K2.u10359 from rfl, allE_node, arows10356, irow10360, arows10359]
  all_goals rfl

theorem atot10360 : totK PD2M8K2 D2M8K2.u10360 = [0, 0, 954129983926, 3291522109276, 2612304963331, 342054192216, 6007061677, 0] := by
  rw [show D2M8K2.u10360 = KTree.node D2M8K2.u10356 (nat_lit 22635082) (nat_lit 3897284932) (nat_lit 0) D2M8K2.u10359 from rfl, totK_node, atot10356, atot10359]
  decide +kernel

theorem arows10371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10371 = true := by
  rw [show D2M8K2.u10371 = KTree.node D2M8K2.u10367 (nat_lit 22645307) (nat_lit 2881265129) (nat_lit 0) D2M8K2.u10370 from rfl, allE_node, arows10367, irow10371, arows10370]
  all_goals rfl

theorem atot10371 : totK PD2M8K2 D2M8K2.u10371 = [0, 0, 755136261409, 2921213521115, 2824884730053, 547637487186, 19903063670, 0] := by
  rw [show D2M8K2.u10371 = KTree.node D2M8K2.u10367 (nat_lit 22645307) (nat_lit 2881265129) (nat_lit 0) D2M8K2.u10370 from rfl, totK_node, atot10367, atot10370]
  decide +kernel

theorem arows10378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10378 = true := by
  rw [show D2M8K2.u10378 = KTree.node D2M8K2.u10374 (nat_lit 22657070) (nat_lit 3510939025) (nat_lit 0) D2M8K2.u10377 from rfl, allE_node, arows10374, irow10378, arows10377]
  all_goals rfl

theorem atot10378 : totK PD2M8K2 D2M8K2.u10378 = [0, 0, 831254050246, 3043536751929, 2758545645595, 478864580477, 14286503612, 0] := by
  rw [show D2M8K2.u10378 = KTree.node D2M8K2.u10374 (nat_lit 22657070) (nat_lit 3510939025) (nat_lit 0) D2M8K2.u10377 from rfl, totK_node, atot10374, atot10377]
  decide +kernel

theorem arows10386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10386 = true := by
  rw [show D2M8K2.u10386 = KTree.node D2M8K2.u10382 (nat_lit 22664388) (nat_lit 2798003289) (nat_lit 0) D2M8K2.u10385 from rfl, allE_node, arows10382, irow10386, arows10385]
  all_goals rfl

theorem atot10386 : totK PD2M8K2 D2M8K2.u10386 = [0, 0, 412273292361, 1955729948931, 3124675052160, 1404653956665, 135624419195, 1310517177] := by
  rw [show D2M8K2.u10386 = KTree.node D2M8K2.u10382 (nat_lit 22664388) (nat_lit 2798003289) (nat_lit 0) D2M8K2.u10385 from rfl, totK_node, atot10382, atot10385]
  decide +kernel

theorem arows10393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10393 = true := by
  rw [show D2M8K2.u10393 = KTree.node D2M8K2.u10389 (nat_lit 22678953) (nat_lit 1907412261) (nat_lit 0) D2M8K2.u10392 from rfl, allE_node, arows10389, irow10393, arows10392]
  all_goals rfl

theorem atot10393 : totK PD2M8K2 D2M8K2.u10393 = [0, 0, 211587284169, 1971408586155, 3621475124069, 1250387819735, 57784331364, 0] := by
  rw [show D2M8K2.u10393 = KTree.node D2M8K2.u10389 (nat_lit 22678953) (nat_lit 1907412261) (nat_lit 0) D2M8K2.u10392 from rfl, totK_node, atot10389, atot10392]
  decide +kernel

theorem arows10402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10402 = true := by
  rw [show D2M8K2.u10402 = KTree.node D2M8K2.u10398 (nat_lit 22692731) (nat_lit 2870304957) (nat_lit 0) D2M8K2.u10401 from rfl, allE_node, arows10398, irow10402, arows10401]
  all_goals rfl

theorem atot10402 : totK PD2M8K2 D2M8K2.u10402 = [0, 0, 984668765185, 3151546224144, 2620358946887, 571429841730, 24743328915, 0] := by
  rw [show D2M8K2.u10402 = KTree.node D2M8K2.u10398 (nat_lit 22692731) (nat_lit 2870304957) (nat_lit 0) D2M8K2.u10401 from rfl, totK_node, atot10398, atot10401]
  decide +kernel

theorem arows10409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10409 = true := by
  rw [show D2M8K2.u10409 = KTree.node D2M8K2.u10405 (nat_lit 22701717) (nat_lit 1734668475) (nat_lit 0) D2M8K2.u10408 from rfl, allE_node, arows10405, irow10409, arows10408]
  all_goals rfl

theorem atot10409 : totK PD2M8K2 D2M8K2.u10409 = [0, 0, 826339742211, 3087734263908, 2818272918542, 519412592360, 17545163470, 0] := by
  rw [show D2M8K2.u10409 = KTree.node D2M8K2.u10405 (nat_lit 22701717) (nat_lit 1734668475) (nat_lit 0) D2M8K2.u10408 from rfl, totK_node, atot10405, atot10408]
  decide +kernel

theorem arows10417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10417 = true := by
  rw [show D2M8K2.u10417 = KTree.node D2M8K2.u10413 (nat_lit 22771945) (nat_lit 1189725006) (nat_lit 0) D2M8K2.u10416 from rfl, allE_node, arows10413, irow10417, arows10416]
  all_goals rfl

theorem atot10417 : totK PD2M8K2 D2M8K2.u10417 = [0, 0, 837721058438, 2936850303362, 2751344468340, 627065186631, 30786671653, 0] := by
  rw [show D2M8K2.u10417 = KTree.node D2M8K2.u10413 (nat_lit 22771945) (nat_lit 1189725006) (nat_lit 0) D2M8K2.u10416 from rfl, totK_node, atot10413, atot10416]
  decide +kernel

theorem arows10424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10424 = true := by
  rw [show D2M8K2.u10424 = KTree.node D2M8K2.u10420 (nat_lit 22781454) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u10423 from rfl, allE_node, arows10420, irow10424, arows10423]
  all_goals rfl

theorem atot10424 : totK PD2M8K2 D2M8K2.u10424 = [0, 0, 862102458839, 2998079013040, 2772524687867, 558732060331, 18586354791, 0] := by
  rw [show D2M8K2.u10424 = KTree.node D2M8K2.u10420 (nat_lit 22781454) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u10423 from rfl, totK_node, atot10420, atot10423]
  decide +kernel

theorem arows10434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10434 = true := by
  rw [show D2M8K2.u10434 = KTree.node D2M8K2.u10430 (nat_lit 22788271) (nat_lit 2180356202) (nat_lit 0) D2M8K2.u10433 from rfl, allE_node, arows10430, irow10434, arows10433]
  all_goals rfl

theorem atot10434 : totK PD2M8K2 D2M8K2.u10434 = [0, 0, 420691460119, 1970011749120, 3078930001234, 1441678369713, 138012532813, 1217496766] := by
  rw [show D2M8K2.u10434 = KTree.node D2M8K2.u10430 (nat_lit 22788271) (nat_lit 2180356202) (nat_lit 0) D2M8K2.u10433 from rfl, totK_node, atot10430, atot10433]
  decide +kernel

theorem arows10441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10441 = true := by
  rw [show D2M8K2.u10441 = KTree.node D2M8K2.u10437 (nat_lit 22800734) (nat_lit 3565502855) (nat_lit 0) D2M8K2.u10440 from rfl, allE_node, arows10437, irow10441, arows10440]
  all_goals rfl

theorem atot10441 : totK PD2M8K2 D2M8K2.u10441 = [0, 0, 0, 1212645219810, 3350808868525, 2171556801737, 359294914886, 13105450397] := by
  rw [show D2M8K2.u10441 = KTree.node D2M8K2.u10437 (nat_lit 22800734) (nat_lit 3565502855) (nat_lit 0) D2M8K2.u10440 from rfl, totK_node, atot10437, atot10440]
  decide +kernel

theorem arows10449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10449 = true := by
  rw [show D2M8K2.u10449 = KTree.node D2M8K2.u10445 (nat_lit 22809714) (nat_lit 3384579950) (nat_lit 0) D2M8K2.u10448 from rfl, allE_node, arows10445, irow10449, arows10448]
  all_goals rfl

theorem atot10449 : totK PD2M8K2 D2M8K2.u10449 = [0, 0, 533094830883, 2167339846400, 2849711164720, 1296248412128, 178276485776, 4630915822] := by
  rw [show D2M8K2.u10449 = KTree.node D2M8K2.u10445 (nat_lit 22809714) (nat_lit 3384579950) (nat_lit 0) D2M8K2.u10448 from rfl, totK_node, atot10445, atot10448]
  decide +kernel

theorem arows10456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10456 = true := by
  rw [show D2M8K2.u10456 = KTree.node D2M8K2.u10452 (nat_lit 22817003) (nat_lit 1926826140) (nat_lit 0) D2M8K2.u10455 from rfl, allE_node, arows10452, irow10456, arows10455]
  all_goals rfl

theorem atot10456 : totK PD2M8K2 D2M8K2.u10456 = [0, 0, 958769250274, 3196139839347, 2550069030336, 483321715285, 19599137318, 0] := by
  rw [show D2M8K2.u10456 = KTree.node D2M8K2.u10452 (nat_lit 22817003) (nat_lit 1926826140) (nat_lit 0) D2M8K2.u10455 from rfl, totK_node, atot10452, atot10455]
  decide +kernel

theorem arows10465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10465 = true := by
  rw [show D2M8K2.u10465 = KTree.node D2M8K2.u10461 (nat_lit 22824450) (nat_lit 3303510607) (nat_lit 0) D2M8K2.u10464 from rfl, allE_node, arows10461, irow10465, arows10464]
  all_goals rfl

theorem atot10465 : totK PD2M8K2 D2M8K2.u10465 = [0, 0, 508530557913, 2483816052493, 3231905100690, 841350703835, 32979760949, 0] := by
  rw [show D2M8K2.u10465 = KTree.node D2M8K2.u10461 (nat_lit 22824450) (nat_lit 3303510607) (nat_lit 0) D2M8K2.u10464 from rfl, totK_node, atot10461, atot10464]
  decide +kernel

theorem arows10472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10472 = true := by
  rw [show D2M8K2.u10472 = KTree.node D2M8K2.u10468 (nat_lit 22838446) (nat_lit 1779556768) (nat_lit 32) D2M8K2.u10471 from rfl, allE_node, arows10468, irow10472, arows10471]
  all_goals rfl

theorem atot10472 : totK PD2M8K2 D2M8K2.u10472 = [0, 0, 0, 1499654571214, 3632602042566, 1708990839912, 132386896255, 1138244013] := by
  rw [show D2M8K2.u10472 = KTree.node D2M8K2.u10468 (nat_lit 22838446) (nat_lit 1779556768) (nat_lit 32) D2M8K2.u10471 from rfl, totK_node, atot10468, atot10471]
  decide +kernel

theorem arows10480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10480 = true := by
  rw [show D2M8K2.u10480 = KTree.node D2M8K2.u10476 (nat_lit 22852555) (nat_lit 1718951419) (nat_lit 0) D2M8K2.u10479 from rfl, allE_node, arows10476, irow10480, arows10479]
  all_goals rfl

theorem atot10480 : totK PD2M8K2 D2M8K2.u10480 = [0, 0, 824328777366, 2624846444811, 2484301091745, 1005981664373, 161766308621, 4914284239] := by
  rw [show D2M8K2.u10480 = KTree.node D2M8K2.u10476 (nat_lit 22852555) (nat_lit 1718951419) (nat_lit 0) D2M8K2.u10479 from rfl, totK_node, atot10476, atot10479]
  decide +kernel

theorem arows10487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10487 = true := by
  rw [show D2M8K2.u10487 = KTree.node D2M8K2.u10483 (nat_lit 22861906) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u10486 from rfl, allE_node, arows10483, irow10487, arows10486]
  all_goals rfl

theorem atot10487 : totK PD2M8K2 D2M8K2.u10487 = [0, 0, 925191728280, 3028442136859, 2693933131261, 625054553721, 25958599549, 0] := by
  rw [show D2M8K2.u10487 = KTree.node D2M8K2.u10483 (nat_lit 22861906) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u10486 from rfl, totK_node, atot10483, atot10486]
  decide +kernel

theorem arows10499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10499 = true := by
  rw [show D2M8K2.u10499 = KTree.node D2M8K2.u10495 (nat_lit 22893131) (nat_lit 2895669219) (nat_lit 0) D2M8K2.u10498 from rfl, allE_node, arows10495, irow10499, arows10498]
  all_goals rfl

theorem atot10499 : totK PD2M8K2 D2M8K2.u10499 = [0, 573337239237, 2120487235287, 2601324292215, 1564495005786, 345938396122, 14338667495, 0] := by
  rw [show D2M8K2.u10499 = KTree.node D2M8K2.u10495 (nat_lit 22893131) (nat_lit 2895669219) (nat_lit 0) D2M8K2.u10498 from rfl, totK_node, atot10495, atot10498]
  decide +kernel

theorem arows10506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10506 = true := by
  rw [show D2M8K2.u10506 = KTree.node D2M8K2.u10502 (nat_lit 22903794) (nat_lit 3450218191) (nat_lit 0) D2M8K2.u10505 from rfl, allE_node, arows10502, irow10506, arows10505]
  all_goals rfl

theorem atot10506 : totK PD2M8K2 D2M8K2.u10506 = [0, 812404635744, 2868997289399, 2801160613563, 639440332755, 26300412495, 0, 0] := by
  rw [show D2M8K2.u10506 = KTree.node D2M8K2.u10502 (nat_lit 22903794) (nat_lit 3450218191) (nat_lit 0) D2M8K2.u10505 from rfl, totK_node, atot10502, atot10505]
  decide +kernel

theorem arows10514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10514 = true := by
  rw [show D2M8K2.u10514 = KTree.node D2M8K2.u10510 (nat_lit 22910769) (nat_lit 1760982295) (nat_lit 0) D2M8K2.u10513 from rfl, allE_node, arows10510, irow10514, arows10513]
  all_goals rfl

theorem atot10514 : totK PD2M8K2 D2M8K2.u10514 = [0, 588178319076, 2600631500321, 3080332524379, 835798432970, 36999144457, 0, 0] := by
  rw [show D2M8K2.u10514 = KTree.node D2M8K2.u10510 (nat_lit 22910769) (nat_lit 1760982295) (nat_lit 0) D2M8K2.u10513 from rfl, totK_node, atot10510, atot10513]
  decide +kernel

theorem arows10521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10521 = true := by
  rw [show D2M8K2.u10521 = KTree.node D2M8K2.u10517 (nat_lit 22921906) (nat_lit 4161564152) (nat_lit 0) D2M8K2.u10520 from rfl, allE_node, arows10517, irow10521, arows10520]
  all_goals rfl

theorem atot10521 : totK PD2M8K2 D2M8K2.u10521 = [0, 0, 1213473994485, 3576269805929, 2052579180889, 188152628268, 1369150432, 0] := by
  rw [show D2M8K2.u10521 = KTree.node D2M8K2.u10517 (nat_lit 22921906) (nat_lit 4161564152) (nat_lit 0) D2M8K2.u10520 from rfl, totK_node, atot10517, atot10520]
  decide +kernel

theorem arows10530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10530 = true := by
  rw [show D2M8K2.u10530 = KTree.node D2M8K2.u10526 (nat_lit 22938796) (nat_lit 3835526670) (nat_lit 0) D2M8K2.u10529 from rfl, allE_node, arows10526, irow10530, arows10529]
  all_goals rfl

theorem atot10530 : totK PD2M8K2 D2M8K2.u10530 = [0, 656091965119, 2449832311631, 3040304559216, 1093648807352, 57018274389, 0, 0] := by
  rw [show D2M8K2.u10530 = KTree.node D2M8K2.u10526 (nat_lit 22938796) (nat_lit 3835526670) (nat_lit 0) D2M8K2.u10529 from rfl, totK_node, atot10526, atot10529]
  decide +kernel

theorem arows10537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10537 = true := by
  rw [show D2M8K2.u10537 = KTree.node D2M8K2.u10533 (nat_lit 22945500) (nat_lit 2758858756) (nat_lit 0) D2M8K2.u10536 from rfl, allE_node, arows10533, irow10537, arows10536]
  all_goals rfl

theorem atot10537 : totK PD2M8K2 D2M8K2.u10537 = [0, 830927565502, 2960560624338, 2814546643613, 618704015655, 25110695650, 0, 0] := by
  rw [show D2M8K2.u10537 = KTree.node D2M8K2.u10533 (nat_lit 22945500) (nat_lit 2758858756) (nat_lit 0) D2M8K2.u10536 from rfl, totK_node, atot10533, atot10536]
  decide +kernel

theorem arows10545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10545 = true := by
  rw [show D2M8K2.u10545 = KTree.node D2M8K2.u10541 (nat_lit 22952407) (nat_lit 2358731816) (nat_lit 0) D2M8K2.u10544 from rfl, allE_node, arows10541, irow10545, arows10544]
  all_goals rfl

theorem atot10545 : totK PD2M8K2 D2M8K2.u10545 = [0, 511116253781, 2476738767415, 3228760190568, 1035311900187, 56975790541, 0, 0] := by
  rw [show D2M8K2.u10545 = KTree.node D2M8K2.u10541 (nat_lit 22952407) (nat_lit 2358731816) (nat_lit 0) D2M8K2.u10544 from rfl, totK_node, atot10541, atot10544]
  decide +kernel

theorem arows10552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10552 = true := by
  rw [show D2M8K2.u10552 = KTree.node D2M8K2.u10548 (nat_lit 22962995) (nat_lit 2015530315) (nat_lit 0) D2M8K2.u10551 from rfl, allE_node, arows10548, irow10552, arows10551]
  all_goals rfl

theorem atot10552 : totK PD2M8K2 D2M8K2.u10552 = [0, 0, 882983891982, 3054207938221, 2738174071927, 574236096245, 19209646827, 0] := by
  rw [show D2M8K2.u10552 = KTree.node D2M8K2.u10548 (nat_lit 22962995) (nat_lit 2015530315) (nat_lit 0) D2M8K2.u10551 from rfl, totK_node, atot10548, atot10551]
  decide +kernel

theorem arows10562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10562 = true := by
  rw [show D2M8K2.u10562 = KTree.node D2M8K2.u10558 (nat_lit 22971714) (nat_lit 2838434719) (nat_lit 0) D2M8K2.u10561 from rfl, allE_node, arows10558, irow10562, arows10561]
  all_goals rfl

theorem atot10562 : totK PD2M8K2 D2M8K2.u10562 = [0, 395430589750, 1745449791245, 2887644233978, 1935458342478, 262208194801, 2602082993, 0] := by
  rw [show D2M8K2.u10562 = KTree.node D2M8K2.u10558 (nat_lit 22971714) (nat_lit 2838434719) (nat_lit 0) D2M8K2.u10561 from rfl, totK_node, atot10558, atot10561]
  decide +kernel

theorem arows10569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10569 = true := by
  rw [show D2M8K2.u10569 = KTree.node D2M8K2.u10565 (nat_lit 22981150) (nat_lit 3138633694) (nat_lit 130) D2M8K2.u10568 from rfl, allE_node, arows10565, irow10569, arows10568]
  all_goals rfl

theorem atot10569 : totK PD2M8K2 D2M8K2.u10569 = [0, 832941259086, 3010413199947, 2856881184309, 578476492761, 16687447040, 0, 0] := by
  rw [show D2M8K2.u10569 = KTree.node D2M8K2.u10565 (nat_lit 22981150) (nat_lit 3138633694) (nat_lit 130) D2M8K2.u10568 from rfl, totK_node, atot10565, atot10568]
  decide +kernel

theorem arows10577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10577 = true := by
  rw [show D2M8K2.u10577 = KTree.node D2M8K2.u10573 (nat_lit 22991053) (nat_lit 1389505568) (nat_lit 0) D2M8K2.u10576 from rfl, allE_node, arows10573, irow10577, arows10576]
  all_goals rfl

theorem atot10577 : totK PD2M8K2 D2M8K2.u10577 = [0, 423287068518, 2247826110548, 3253194569513, 1102683120530, 78162390666, 1206465782, 0] := by
  rw [show D2M8K2.u10577 = KTree.node D2M8K2.u10573 (nat_lit 22991053) (nat_lit 1389505568) (nat_lit 0) D2M8K2.u10576 from rfl, totK_node, atot10573, atot10576]
  decide +kernel

theorem arows10584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10584 = true := by
  rw [show D2M8K2.u10584 = KTree.node D2M8K2.u10580 (nat_lit 23003755) (nat_lit 1487285330) (nat_lit 0) D2M8K2.u10583 from rfl, allE_node, arows10580, irow10584, arows10583]
  all_goals rfl

theorem atot10584 : totK PD2M8K2 D2M8K2.u10584 = [0, 0, 1250313726780, 3606322902610, 2109690835064, 175592479670, 1021600638, 0] := by
  rw [show D2M8K2.u10584 = KTree.node D2M8K2.u10580 (nat_lit 23003755) (nat_lit 1487285330) (nat_lit 0) D2M8K2.u10583 from rfl, totK_node, atot10580, atot10583]
  decide +kernel

theorem arows10593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10593 = true := by
  rw [show D2M8K2.u10593 = KTree.node D2M8K2.u10589 (nat_lit 23019664) (nat_lit 2408988461) (nat_lit 0) D2M8K2.u10592 from rfl, allE_node, arows10589, irow10593, arows10592]
  all_goals rfl

theorem atot10593 : totK PD2M8K2 D2M8K2.u10593 = [0, 825849334522, 2735036519932, 2604114151067, 901949950479, 118426668821, 3552795014, 0] := by
  rw [show D2M8K2.u10593 = KTree.node D2M8K2.u10589 (nat_lit 23019664) (nat_lit 2408988461) (nat_lit 0) D2M8K2.u10592 from rfl, totK_node, atot10589, atot10592]
  decide +kernel

theorem arows10600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10600 = true := by
  rw [show D2M8K2.u10600 = KTree.node D2M8K2.u10596 (nat_lit 23029373) (nat_lit 2072770191) (nat_lit 0) D2M8K2.u10599 from rfl, allE_node, arows10596, irow10600, arows10599]
  all_goals rfl

theorem atot10600 : totK PD2M8K2 D2M8K2.u10600 = [0, 865290922124, 2918264862917, 2768058115699, 681578192191, 24038965354, 0, 0] := by
  rw [show D2M8K2.u10600 = KTree.node D2M8K2.u10596 (nat_lit 23029373) (nat_lit 2072770191) (nat_lit 0) D2M8K2.u10599 from rfl, totK_node, atot10596, atot10599]
  decide +kernel

theorem arows10608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10608 = true := by
  rw [show D2M8K2.u10608 = KTree.node D2M8K2.u10604 (nat_lit 23036843) (nat_lit 2886763131) (nat_lit 0) D2M8K2.u10607 from rfl, allE_node, arows10604, irow10608, arows10607]
  all_goals rfl

theorem atot10608 : totK PD2M8K2 D2M8K2.u10608 = [0, 345725408665, 1986679441632, 3262653315571, 1426826303092, 125651018252, 1239866073, 0] := by
  rw [show D2M8K2.u10608 = KTree.node D2M8K2.u10604 (nat_lit 23036843) (nat_lit 2886763131) (nat_lit 0) D2M8K2.u10607 from rfl, totK_node, atot10604, atot10607]
  decide +kernel

theorem arows10615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10615 = true := by
  rw [show D2M8K2.u10615 = KTree.node D2M8K2.u10611 (nat_lit 23049107) (nat_lit 2715031670) (nat_lit 0) D2M8K2.u10614 from rfl, allE_node, arows10611, irow10615, arows10614]
  all_goals rfl

theorem atot10615 : totK PD2M8K2 D2M8K2.u10615 = [0, 0, 1097816097441, 3291571379075, 2408939267288, 389682978771, 13105450397, 0] := by
  rw [show D2M8K2.u10615 = KTree.node D2M8K2.u10611 (nat_lit 23049107) (nat_lit 2715031670) (nat_lit 0) D2M8K2.u10614 from rfl, totK_node, atot10611, atot10614]
  decide +kernel

theorem arows10626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10626 = true := by
  rw [show D2M8K2.u10626 = KTree.node D2M8K2.u10622 (nat_lit 23056105) (nat_lit 1442564089) (nat_lit 0) D2M8K2.u10625 from rfl, allE_node, arows10622, irow10626, arows10625]
  all_goals rfl

theorem atot10626 : totK PD2M8K2 D2M8K2.u10626 = [0, 412433268895, 1916795199192, 2940968983458, 1621009405902, 212537767286, 4720618446, 0] := by
  rw [show D2M8K2.u10626 = KTree.node D2M8K2.u10622 (nat_lit 23056105) (nat_lit 1442564089) (nat_lit 0) D2M8K2.u10625 from rfl, totK_node, atot10622, atot10625]
  decide +kernel

theorem arows10633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10633 = true := by
  rw [show D2M8K2.u10633 = KTree.node D2M8K2.u10629 (nat_lit 23064724) (nat_lit 2702185241) (nat_lit 0) D2M8K2.u10632 from rfl, allE_node, arows10629, irow10633, arows10632]
  all_goals rfl

theorem atot10633 : totK PD2M8K2 D2M8K2.u10633 = [0, 823673394653, 2840027340806, 2764154378479, 745600647819, 37124307499, 0, 0] := by
  rw [show D2M8K2.u10633 = KTree.node D2M8K2.u10629 (nat_lit 23064724) (nat_lit 2702185241) (nat_lit 0) D2M8K2.u10632 from rfl, totK_node, atot10629, atot10632]
  decide +kernel

theorem arows10641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10641 = true := by
  rw [show D2M8K2.u10641 = KTree.node D2M8K2.u10637 (nat_lit 23071466) (nat_lit 4080338093) (nat_lit 0) D2M8K2.u10640 from rfl, allE_node, arows10637, irow10641, arows10640]
  all_goals rfl

theorem atot10641 : totK PD2M8K2 D2M8K2.u10641 = [0, 866248944588, 2930293725246, 2757731557605, 632070944091, 26232597979, 0, 0] := by
  rw [show D2M8K2.u10641 = KTree.node D2M8K2.u10637 (nat_lit 23071466) (nat_lit 4080338093) (nat_lit 0) D2M8K2.u10640 from rfl, totK_node, atot10637, atot10640]
  decide +kernel

theorem arows10648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10648 = true := by
  rw [show D2M8K2.u10648 = KTree.node D2M8K2.u10644 (nat_lit 23081841) (nat_lit 1836478434) (nat_lit 0) D2M8K2.u10647 from rfl, allE_node, arows10644, irow10648, arows10647]
  all_goals rfl

theorem atot10648 : totK PD2M8K2 D2M8K2.u10648 = [0, 0, 1390071428998, 3645973173438, 1891902023876, 166414376520, 1138244013, 0] := by
  rw [show D2M8K2.u10648 = KTree.node D2M8K2.u10644 (nat_lit 23081841) (nat_lit 1836478434) (nat_lit 0) D2M8K2.u10647 from rfl, totK_node, atot10644, atot10647]
  decide +kernel

theorem arows10657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10657 = true := by
  rw [show D2M8K2.u10657 = KTree.node D2M8K2.u10653 (nat_lit 23093494) (nat_lit 2209708654) (nat_lit 0) D2M8K2.u10656 from rfl, allE_node, arows10653, irow10657, arows10656]
  all_goals rfl

theorem atot10657 : totK PD2M8K2 D2M8K2.u10657 = [0, 0, 1177102632589, 3466691010624, 2193190534840, 272949190617, 4977114383, 0] := by
  rw [show D2M8K2.u10657 = KTree.node D2M8K2.u10653 (nat_lit 23093494) (nat_lit 2209708654) (nat_lit 0) D2M8K2.u10656 from rfl, totK_node, atot10653, atot10656]
  decide +kernel

theorem arows10664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10664 = true := by
  rw [show D2M8K2.u10664 = KTree.node D2M8K2.u10660 (nat_lit 23149065) (nat_lit 1757933004) (nat_lit 0) D2M8K2.u10663 from rfl, allE_node, arows10660, irow10664, arows10663]
  all_goals rfl

theorem atot10664 : totK PD2M8K2 D2M8K2.u10664 = [0, 0, 1007197535068, 3313436283585, 2535188044534, 270519710326, 2533470052, 0] := by
  rw [show D2M8K2.u10664 = KTree.node D2M8K2.u10660 (nat_lit 23149065) (nat_lit 1757933004) (nat_lit 0) D2M8K2.u10663 from rfl, totK_node, atot10660, atot10663]
  decide +kernel

theorem arows10672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10672 = true := by
  rw [show D2M8K2.u10672 = KTree.node D2M8K2.u10668 (nat_lit 23156391) (nat_lit 3597753314) (nat_lit 0) D2M8K2.u10671 from rfl, allE_node, arows10668, irow10672, arows10671]
  all_goals rfl

theorem atot10672 : totK PD2M8K2 D2M8K2.u10672 = [0, 0, 778786707230, 2932083056269, 2816233647114, 545976599572, 19433571662, 0] := by
  rw [show D2M8K2.u10672 = KTree.node D2M8K2.u10668 (nat_lit 23156391) (nat_lit 3597753314) (nat_lit 0) D2M8K2.u10671 from rfl, totK_node, atot10668, atot10671]
  decide +kernel

theorem arows10679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10679 = true := by
  rw [show D2M8K2.u10679 = KTree.node D2M8K2.u10675 (nat_lit 23165405) (nat_lit 1495703429) (nat_lit 32) D2M8K2.u10678 from rfl, allE_node, arows10675, irow10679, arows10678]
  all_goals rfl

theorem atot10679 : totK PD2M8K2 D2M8K2.u10679 = [0, 0, 0, 1589297530862, 3739790651772, 1502077450662, 106686616941, 1209030869] := by
  rw [show D2M8K2.u10679 = KTree.node D2M8K2.u10675 (nat_lit 23165405) (nat_lit 1495703429) (nat_lit 32) D2M8K2.u10678 from rfl, totK_node, atot10675, atot10678]
  decide +kernel

theorem arows10689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10689 = true := by
  rw [show D2M8K2.u10689 = KTree.node D2M8K2.u10685 (nat_lit 23187417) (nat_lit 1873276985) (nat_lit 0) D2M8K2.u10688 from rfl, allE_node, arows10685, irow10689, arows10688]
  all_goals rfl

theorem atot10689 : totK PD2M8K2 D2M8K2.u10689 = [0, 0, 704572218132, 2707988632557, 3030501428036, 792900390704, 31592451853, 0] := by
  rw [show D2M8K2.u10689 = KTree.node D2M8K2.u10685 (nat_lit 23187417) (nat_lit 1873276985) (nat_lit 0) D2M8K2.u10688 from rfl, totK_node, atot10685, atot10688]
  decide +kernel

theorem arows10696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10696 = true := by
  rw [show D2M8K2.u10696 = KTree.node D2M8K2.u10692 (nat_lit 23196248) (nat_lit 3517071465) (nat_lit 0) D2M8K2.u10695 from rfl, allE_node, arows10692, irow10696, arows10695]
  all_goals rfl

theorem atot10696 : totK PD2M8K2 D2M8K2.u10696 = [0, 0, 954316063236, 3237571152927, 2670459159676, 407287069450, 9882685783, 0] := by
  rw [show D2M8K2.u10696 = KTree.node D2M8K2.u10692 (nat_lit 23196248) (nat_lit 3517071465) (nat_lit 0) D2M8K2.u10695 from rfl, totK_node, atot10692, atot10695]
  decide +kernel

theorem arows10704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10704 = true := by
  rw [show D2M8K2.u10704 = KTree.node D2M8K2.u10700 (nat_lit 23226201) (nat_lit 1696710943) (nat_lit 0) D2M8K2.u10703 from rfl, allE_node, arows10700, irow10704, arows10703]
  all_goals rfl

theorem atot10704 : totK PD2M8K2 D2M8K2.u10704 = [0, 0, 1394184568283, 3605984243886, 2087542758087, 203564179582, 4123500472, 0] := by
  rw [show D2M8K2.u10704 = KTree.node D2M8K2.u10700 (nat_lit 23226201) (nat_lit 1696710943) (nat_lit 0) D2M8K2.u10703 from rfl, totK_node, atot10700, atot10703]
  decide +kernel

theorem arows10711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10711 = true := by
  rw [show D2M8K2.u10711 = KTree.node D2M8K2.u10707 (nat_lit 23239043) (nat_lit 1349679449) (nat_lit 2080) D2M8K2.u10710 from rfl, allE_node, arows10707, irow10711, arows10710]
  all_goals rfl

theorem atot10711 : totK PD2M8K2 D2M8K2.u10711 = [0, 0, 905928537079, 3199374142355, 2595586268022, 381123110034, 9606848709, 0] := by
  rw [show D2M8K2.u10711 = KTree.node D2M8K2.u10707 (nat_lit 23239043) (nat_lit 1349679449) (nat_lit 2080) D2M8K2.u10710 from rfl, totK_node, atot10707, atot10710]
  decide +kernel

theorem arows10720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10720 = true := by
  rw [show D2M8K2.u10720 = KTree.node D2M8K2.u10716 (nat_lit 23270966) (nat_lit 3184346391) (nat_lit 0) D2M8K2.u10719 from rfl, allE_node, arows10716, irow10720, arows10719]
  all_goals rfl

theorem atot10720 : totK PD2M8K2 D2M8K2.u10720 = [0, 0, 933088951619, 3119618632565, 2720061626139, 502134978468, 16376849850, 0] := by
  rw [show D2M8K2.u10720 = KTree.node D2M8K2.u10716 (nat_lit 23270966) (nat_lit 3184346391) (nat_lit 0) D2M8K2.u10719 from rfl, totK_node, atot10716, atot10719]
  decide +kernel

theorem arows10727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10727 = true := by
  rw [show D2M8K2.u10727 = KTree.node D2M8K2.u10723 (nat_lit 23280830) (nat_lit 3781039000) (nat_lit 0) D2M8K2.u10726 from rfl, allE_node, arows10723, irow10727, arows10726]
  all_goals rfl

theorem atot10727 : totK PD2M8K2 D2M8K2.u10727 = [0, 0, 762640236780, 2916432516616, 2913676045868, 568659800997, 18151190877, 0] := by
  rw [show D2M8K2.u10727 = KTree.node D2M8K2.u10723 (nat_lit 23280830) (nat_lit 3781039000) (nat_lit 0) D2M8K2.u10726 from rfl, totK_node, atot10723, atot10726]
  decide +kernel

theorem arows10735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10735 = true := by
  rw [show D2M8K2.u10735 = KTree.node D2M8K2.u10731 (nat_lit 23309866) (nat_lit 3780063444) (nat_lit 0) D2M8K2.u10734 from rfl, allE_node, arows10731, irow10735, arows10734]
  all_goals rfl

theorem atot10735 : totK PD2M8K2 D2M8K2.u10735 = [0, 0, 826372478057, 2990620959703, 2781974410011, 530146802862, 18831319709, 0] := by
  rw [show D2M8K2.u10735 = KTree.node D2M8K2.u10731 (nat_lit 23309866) (nat_lit 3780063444) (nat_lit 0) D2M8K2.u10734 from rfl, totK_node, atot10731, atot10734]
  decide +kernel

theorem arows10742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10742 = true := by
  rw [show D2M8K2.u10742 = KTree.node D2M8K2.u10738 (nat_lit 23317296) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u10741 from rfl, allE_node, arows10738, irow10742, arows10741]
  all_goals rfl

theorem atot10742 : totK PD2M8K2 D2M8K2.u10742 = [0, 0, 812968522178, 2935790288886, 2784403539598, 548575243747, 17685503241, 0] := by
  rw [show D2M8K2.u10742 = KTree.node D2M8K2.u10738 (nat_lit 23317296) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u10741 from rfl, totK_node, atot10738, atot10741]
  decide +kernel

theorem arows10755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10755 = true := by
  rw [show D2M8K2.u10755 = KTree.node D2M8K2.u10751 (nat_lit 23324030) (nat_lit 3661376432) (nat_lit 0) D2M8K2.u10754 from rfl, allE_node, arows10751, irow10755, arows10754]
  all_goals rfl

theorem atot10755 : totK PD2M8K2 D2M8K2.u10755 = [0, 0, 441947594641, 2124274678762, 3134202459153, 1231557071060, 104807127105, 1138244013] := by
  rw [show D2M8K2.u10755 = KTree.node D2M8K2.u10751 (nat_lit 23324030) (nat_lit 3661376432) (nat_lit 0) D2M8K2.u10754 from rfl, totK_node, atot10751, atot10754]
  decide +kernel

theorem arows10762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10762 = true := by
  rw [show D2M8K2.u10762 = KTree.node D2M8K2.u10758 (nat_lit 23339359) (nat_lit 2367312987) (nat_lit 0) D2M8K2.u10761 from rfl, allE_node, arows10758, irow10762, arows10761]
  all_goals rfl

theorem atot10762 : totK PD2M8K2 D2M8K2.u10762 = [0, 0, 0, 1555421025128, 3680358695645, 1662287088037, 131283797392, 1095107716] := by
  rw [show D2M8K2.u10762 = KTree.node D2M8K2.u10758 (nat_lit 23339359) (nat_lit 2367312987) (nat_lit 0) D2M8K2.u10761 from rfl, totK_node, atot10758, atot10761]
  decide +kernel

theorem arows10770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10770 = true := by
  rw [show D2M8K2.u10770 = KTree.node D2M8K2.u10766 (nat_lit 23393096) (nat_lit 3697004479) (nat_lit 0) D2M8K2.u10769 from rfl, allE_node, arows10766, irow10770, arows10769]
  all_goals rfl

theorem atot10770 : totK PD2M8K2 D2M8K2.u10770 = [0, 814826583167, 2849010337011, 2501935883395, 571388487664, 325512023245, 93467172928, 3882006667] := by
  rw [show D2M8K2.u10770 = KTree.node D2M8K2.u10766 (nat_lit 23393096) (nat_lit 3697004479) (nat_lit 0) D2M8K2.u10769 from rfl, totK_node, atot10766, atot10769]
  decide +kernel

theorem arows10777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10777 = true := by
  rw [show D2M8K2.u10777 = KTree.node D2M8K2.u10773 (nat_lit 23403775) (nat_lit 2300529621) (nat_lit 0) D2M8K2.u10776 from rfl, allE_node, arows10773, irow10777, arows10776]
  all_goals rfl

theorem atot10777 : totK PD2M8K2 D2M8K2.u10777 = [0, 899103334054, 3036501558477, 2673277041467, 552328712271, 18231200220, 0, 0] := by
  rw [show D2M8K2.u10777 = KTree.node D2M8K2.u10773 (nat_lit 23403775) (nat_lit 2300529621) (nat_lit 0) D2M8K2.u10776 from rfl, totK_node, atot10773, atot10776]
  decide +kernel

theorem arows10786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10786 = true := by
  rw [show D2M8K2.u10786 = KTree.node D2M8K2.u10782 (nat_lit 23411147) (nat_lit 2331704174) (nat_lit 0) D2M8K2.u10785 from rfl, allE_node, arows10782, irow10786, arows10785]
  all_goals rfl

theorem atot10786 : totK PD2M8K2 D2M8K2.u10786 = [0, 264732260305, 1693609382112, 3251078767137, 1681991361007, 173784752144, 1369150432, 0] := by
  rw [show D2M8K2.u10786 = KTree.node D2M8K2.u10782 (nat_lit 23411147) (nat_lit 2331704174) (nat_lit 0) D2M8K2.u10785 from rfl, totK_node, atot10782, atot10785]
  decide +kernel

theorem arows10793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10793 = true := by
  rw [show D2M8K2.u10793 = KTree.node D2M8K2.u10789 (nat_lit 23425042) (nat_lit 3852090700) (nat_lit 0) D2M8K2.u10792 from rfl, allE_node, arows10789, irow10793, arows10792]
  all_goals rfl

theorem atot10793 : totK PD2M8K2 D2M8K2.u10793 = [0, 94311201580, 1608233409775, 3691526122054, 1688784144719, 86910618435, 0, 0] := by
  rw [show D2M8K2.u10793 = KTree.node D2M8K2.u10789 (nat_lit 23425042) (nat_lit 3852090700) (nat_lit 0) D2M8K2.u10792 from rfl, totK_node, atot10789, atot10792]
  decide +kernel

theorem arows10801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10801 = true := by
  rw [show D2M8K2.u10801 = KTree.node D2M8K2.u10797 (nat_lit 23438345) (nat_lit 1763142559) (nat_lit 0) D2M8K2.u10800 from rfl, allE_node, arows10797, irow10801, arows10800]
  all_goals rfl

theorem atot10801 : totK PD2M8K2 D2M8K2.u10801 = [0, 734223398510, 2709475466470, 2911791951720, 874298330421, 47089223176, 0, 0] := by
  rw [show D2M8K2.u10801 = KTree.node D2M8K2.u10797 (nat_lit 23438345) (nat_lit 1763142559) (nat_lit 0) D2M8K2.u10800 from rfl, totK_node, atot10797, atot10800]
  decide +kernel

theorem arows10808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10808 = true := by
  rw [show D2M8K2.u10808 = KTree.node D2M8K2.u10804 (nat_lit 23445242) (nat_lit 4210269236) (nat_lit 0) D2M8K2.u10807 from rfl, allE_node, arows10804, irow10808, arows10807]
  all_goals rfl

theorem atot10808 : totK PD2M8K2 D2M8K2.u10808 = [0, 909437160876, 3102754351344, 2789230988514, 538263857594, 16008134795, 0, 0] := by
  rw [show D2M8K2.u10808 = KTree.node D2M8K2.u10804 (nat_lit 23445242) (nat_lit 4210269236) (nat_lit 0) D2M8K2.u10807 from rfl, totK_node, atot10804, atot10807]
  decide +kernel

theorem arows10818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10818 = true := by
  rw [show D2M8K2.u10818 = KTree.node D2M8K2.u10814 (nat_lit 23456363) (nat_lit 2717758855) (nat_lit 0) D2M8K2.u10817 from rfl, allE_node, arows10814, irow10818, arows10817]
  all_goals rfl

theorem atot10818 : totK PD2M8K2 D2M8K2.u10818 = [0, 265593258125, 1567961746557, 2925564056205, 1977686664217, 474923412431, 26567849899, 0] := by
  rw [show D2M8K2.u10818 = KTree.node D2M8K2.u10814 (nat_lit 23456363) (nat_lit 2717758855) (nat_lit 0) D2M8K2.u10817 from rfl, totK_node, atot10814, atot10817]
  decide +kernel

theorem arows10825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10825 = true := by
  rw [show D2M8K2.u10825 = KTree.node D2M8K2.u10821 (nat_lit 23463033) (nat_lit 1827566638) (nat_lit 0) D2M8K2.u10824 from rfl, allE_node, arows10821, irow10825, arows10824]
  all_goals rfl

theorem atot10825 : totK PD2M8K2 D2M8K2.u10825 = [0, 0, 890397539500, 3090992244106, 2770986503291, 521660419440, 13290796749, 0] := by
  rw [show D2M8K2.u10825 = KTree.node D2M8K2.u10821 (nat_lit 23463033) (nat_lit 1827566638) (nat_lit 0) D2M8K2.u10824 from rfl, totK_node, atot10821, atot10824]
  decide +kernel

theorem arows10833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10833 = true := by
  rw [show D2M8K2.u10833 = KTree.node D2M8K2.u10829 (nat_lit 23470690) (nat_lit 4141497652) (nat_lit 0) D2M8K2.u10832 from rfl, allE_node, arows10829, irow10833, arows10832]
  all_goals rfl

theorem atot10833 : totK PD2M8K2 D2M8K2.u10833 = [0, 309149030834, 1397788749729, 2762998574606, 2312112665217, 445910325703, 10717512769, 0] := by
  rw [show D2M8K2.u10833 = KTree.node D2M8K2.u10829 (nat_lit 23470690) (nat_lit 4141497652) (nat_lit 0) D2M8K2.u10832 from rfl, totK_node, atot10829, atot10832]
  decide +kernel

theorem arows10840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10840 = true := by
  rw [show D2M8K2.u10840 = KTree.node D2M8K2.u10836 (nat_lit 23478180) (nat_lit 3145530091) (nat_lit 0) D2M8K2.u10839 from rfl, allE_node, arows10836, irow10840, arows10839]
  all_goals rfl

theorem atot10840 : totK PD2M8K2 D2M8K2.u10840 = [0, 795296328969, 2841172253059, 2866691690534, 738616840295, 34949709642, 0, 0] := by
  rw [show D2M8K2.u10840 = KTree.node D2M8K2.u10836 (nat_lit 23478180) (nat_lit 3145530091) (nat_lit 0) D2M8K2.u10839 from rfl, totK_node, atot10836, atot10839]
  decide +kernel

theorem arows10849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10849 = true := by
  rw [show D2M8K2.u10849 = KTree.node D2M8K2.u10845 (nat_lit 23491341) (nat_lit 1213001456) (nat_lit 0) D2M8K2.u10848 from rfl, allE_node, arows10845, irow10849, arows10848]
  all_goals rfl

theorem atot10849 : totK PD2M8K2 D2M8K2.u10849 = [0, 553264517824, 2558117247662, 3182882541746, 885373412099, 37246663167, 0, 0] := by
  rw [show D2M8K2.u10849 = KTree.node D2M8K2.u10845 (nat_lit 23491341) (nat_lit 1213001456) (nat_lit 0) D2M8K2.u10848 from rfl, totK_node, atot10845, atot10848]
  decide +kernel

theorem arows10856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10856 = true := by
  rw [show D2M8K2.u10856 = KTree.node D2M8K2.u10852 (nat_lit 23498834) (nat_lit 4049472801) (nat_lit 0) D2M8K2.u10855 from rfl, allE_node, arows10852, irow10856, arows10855]
  all_goals rfl

theorem atot10856 : totK PD2M8K2 D2M8K2.u10856 = [0, 0, 985729373592, 3310919378979, 2518116998614, 327193536808, 6601594569, 0] := by
  rw [show D2M8K2.u10856 = KTree.node D2M8K2.u10852 (nat_lit 23498834) (nat_lit 4049472801) (nat_lit 0) D2M8K2.u10855 from rfl, totK_node, atot10852, atot10855]
  decide +kernel

theorem arows10864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10864 = true := by
  rw [show D2M8K2.u10864 = KTree.node D2M8K2.u10860 (nat_lit 23515868) (nat_lit 3395784958) (nat_lit 0) D2M8K2.u10863 from rfl, allE_node, arows10860, irow10864, arows10863]
  all_goals rfl

theorem atot10864 : totK PD2M8K2 D2M8K2.u10864 = [0, 753428134686, 2727102338582, 2839671177432, 860524775516, 57305234663, 0, 0] := by
  rw [show D2M8K2.u10864 = KTree.node D2M8K2.u10860 (nat_lit 23515868) (nat_lit 3395784958) (nat_lit 0) D2M8K2.u10863 from rfl, totK_node, atot10860, atot10863]
  decide +kernel

theorem arows10871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10871 = true := by
  rw [show D2M8K2.u10871 = KTree.node D2M8K2.u10867 (nat_lit 23525999) (nat_lit 2763433551) (nat_lit 0) D2M8K2.u10870 from rfl, allE_node, arows10867, irow10871, arows10870]
  all_goals rfl

theorem atot10871 : totK PD2M8K2 D2M8K2.u10871 = [0, 695668331398, 2640448276314, 2965695209815, 926516821451, 49271528162, 0, 0] := by
  rw [show D2M8K2.u10871 = KTree.node D2M8K2.u10867 (nat_lit 23525999) (nat_lit 2763433551) (nat_lit 0) D2M8K2.u10870 from rfl, totK_node, atot10867, atot10870]
  decide +kernel

theorem arows10882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10882 = true := by
  rw [show D2M8K2.u10882 = KTree.node D2M8K2.u10878 (nat_lit 23532997) (nat_lit 1198269861) (nat_lit 0) D2M8K2.u10881 from rfl, allE_node, arows10878, irow10882, arows10881]
  all_goals rfl

theorem atot10882 : totK PD2M8K2 D2M8K2.u10882 = [0, 587450886773, 2567890552778, 3124746296104, 890706386623, 38106162904, 0, 0] := by
  rw [show D2M8K2.u10882 = KTree.node D2M8K2.u10878 (nat_lit 23532997) (nat_lit 1198269861) (nat_lit 0) D2M8K2.u10881 from rfl, totK_node, atot10878, atot10881]
  decide +kernel

theorem arows10889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10889 = true := by
  rw [show D2M8K2.u10889 = KTree.node D2M8K2.u10885 (nat_lit 23540285) (nat_lit 2194667363) (nat_lit 0) D2M8K2.u10888 from rfl, allE_node, arows10885, irow10889, arows10888]
  all_goals rfl

theorem atot10889 : totK PD2M8K2 D2M8K2.u10889 = [0, 0, 1005145841152, 3244382414055, 2533008450919, 385380841074, 10873128647, 0] := by
  rw [show D2M8K2.u10889 = KTree.node D2M8K2.u10885 (nat_lit 23540285) (nat_lit 2194667363) (nat_lit 0) D2M8K2.u10888 from rfl, totK_node, atot10885, atot10888]
  decide +kernel

theorem arows10897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10897 = true := by
  rw [show D2M8K2.u10897 = KTree.node D2M8K2.u10893 (nat_lit 23552779) (nat_lit 1617497951) (nat_lit 0) D2M8K2.u10896 from rfl, allE_node, arows10893, irow10897, arows10896]
  all_goals rfl

theorem atot10897 : totK PD2M8K2 D2M8K2.u10897 = [0, 369552279963, 1655651934696, 2854129770623, 1933438905980, 305298695604, 8192806269, 0] := by
  rw [show D2M8K2.u10897 = KTree.node D2M8K2.u10893 (nat_lit 23552779) (nat_lit 1617497951) (nat_lit 0) D2M8K2.u10896 from rfl, totK_node, atot10893, atot10896]
  decide +kernel

theorem arows10904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10904 = true := by
  rw [show D2M8K2.u10904 = KTree.node D2M8K2.u10900 (nat_lit 23602636) (nat_lit 3831009219) (nat_lit 0) D2M8K2.u10903 from rfl, allE_node, arows10900, irow10904, arows10903]
  all_goals rfl

theorem atot10904 : totK PD2M8K2 D2M8K2.u10904 = [0, 743426702366, 2788423855873, 2898416177879, 773861901016, 37337762172, 0, 0] := by
  rw [show D2M8K2.u10904 = KTree.node D2M8K2.u10900 (nat_lit 23602636) (nat_lit 3831009219) (nat_lit 0) D2M8K2.u10903 from rfl, totK_node, atot10900, atot10903]
  decide +kernel

theorem arows10913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10913 = true := by
  rw [show D2M8K2.u10913 = KTree.node D2M8K2.u10909 (nat_lit 23609132) (nat_lit 3532033638) (nat_lit 0) D2M8K2.u10912 from rfl, allE_node, arows10909, irow10913, arows10912]
  all_goals rfl

theorem atot10913 : totK PD2M8K2 D2M8K2.u10913 = [0, 813634334713, 2905602078118, 2857473167142, 635515161601, 22028772465, 0, 0] := by
  rw [show D2M8K2.u10913 = KTree.node D2M8K2.u10909 (nat_lit 23609132) (nat_lit 3532033638) (nat_lit 0) D2M8K2.u10912 from rfl, totK_node, atot10909, atot10912]
  decide +kernel

theorem arows10920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10920 = true := by
  rw [show D2M8K2.u10920 = KTree.node D2M8K2.u10916 (nat_lit 23619089) (nat_lit 1689377152) (nat_lit 0) D2M8K2.u10919 from rfl, allE_node, arows10916, irow10920, arows10919]
  all_goals rfl

theorem atot10920 : totK PD2M8K2 D2M8K2.u10920 = [0, 182497872290, 1593645063429, 3323140439402, 1885798284741, 181543867512, 1310285577, 0] := by
  rw [show D2M8K2.u10920 = KTree.node D2M8K2.u10916 (nat_lit 23619089) (nat_lit 1689377152) (nat_lit 0) D2M8K2.u10919 from rfl, totK_node, atot10916, atot10919]
  decide +kernel

theorem arows10928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10928 = true := by
  rw [show D2M8K2.u10928 = KTree.node D2M8K2.u10924 (nat_lit 23627552) (nat_lit 3430332264) (nat_lit 0) D2M8K2.u10927 from rfl, allE_node, arows10924, irow10928, arows10927]
  all_goals rfl

theorem atot10928 : totK PD2M8K2 D2M8K2.u10928 = [0, 0, 990533276114, 3262990498410, 2541731187776, 357657868653, 5986997553, 0] := by
  rw [show D2M8K2.u10928 = KTree.node D2M8K2.u10924 (nat_lit 23627552) (nat_lit 3430332264) (nat_lit 0) D2M8K2.u10927 from rfl, totK_node, atot10924, atot10927]
  decide +kernel

theorem arows10935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10935 = true := by
  rw [show D2M8K2.u10935 = KTree.node D2M8K2.u10931 (nat_lit 23638081) (nat_lit 1366875701) (nat_lit 0) D2M8K2.u10934 from rfl, allE_node, arows10931, irow10935, arows10934]
  all_goals rfl

theorem atot10935 : totK PD2M8K2 D2M8K2.u10935 = [442400928062, 1270137119403, 1289689357001, 1841329696349, 1830230252442, 490675632114, 24521588297, 0] := by
  rw [show D2M8K2.u10935 = KTree.node D2M8K2.u10931 (nat_lit 23638081) (nat_lit 1366875701) (nat_lit 0) D2M8K2.u10934 from rfl, totK_node, atot10931, atot10934]
  decide +kernel

theorem arows10945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10945 = true := by
  rw [show D2M8K2.u10945 = KTree.node D2M8K2.u10941 (nat_lit 23897150) (nat_lit 3796942699) (nat_lit 0) D2M8K2.u10944 from rfl, allE_node, arows10941, irow10945, arows10944]
  all_goals rfl

theorem atot10945 : totK PD2M8K2 D2M8K2.u10945 = [833425195487, 2992634860883, 2805047880163, 522154061971, 14247800626, 0, 0, 0] := by
  rw [show D2M8K2.u10945 = KTree.node D2M8K2.u10941 (nat_lit 23897150) (nat_lit 3796942699) (nat_lit 0) D2M8K2.u10944 from rfl, totK_node, atot10941, atot10944]
  decide +kernel

theorem arows10952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10952 = true := by
  rw [show D2M8K2.u10952 = KTree.node D2M8K2.u10948 (nat_lit 23903784) (nat_lit 2565638099) (nat_lit 0) D2M8K2.u10951 from rfl, allE_node, arows10948, irow10952, arows10951]
  all_goals rfl

theorem atot10952 : totK PD2M8K2 D2M8K2.u10952 = [821113459690, 2934903348872, 2801163447788, 578440596914, 18301866131, 0, 0, 0] := by
  rw [show D2M8K2.u10952 = KTree.node D2M8K2.u10948 (nat_lit 23903784) (nat_lit 2565638099) (nat_lit 0) D2M8K2.u10951 from rfl, totK_node, atot10948, atot10951]
  decide +kernel

theorem arows10960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10960 = true := by
  rw [show D2M8K2.u10960 = KTree.node D2M8K2.u10956 (nat_lit 23910474) (nat_lit 3370762220) (nat_lit 0) D2M8K2.u10959 from rfl, allE_node, arows10956, irow10960, arows10959]
  all_goals rfl

theorem atot10960 : totK PD2M8K2 D2M8K2.u10960 = [0, 1239508730827, 3525688793684, 2071688941180, 213150615069, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10960 = KTree.node D2M8K2.u10956 (nat_lit 23910474) (nat_lit 3370762220) (nat_lit 0) D2M8K2.u10959 from rfl, totK_node, atot10956, atot10959]
  decide +kernel

theorem arows10967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10967 = true := by
  rw [show D2M8K2.u10967 = KTree.node D2M8K2.u10963 (nat_lit 23925972) (nat_lit 3256651690) (nat_lit 0) D2M8K2.u10966 from rfl, allE_node, arows10963, irow10967, arows10966]
  all_goals rfl

theorem atot10967 : totK PD2M8K2 D2M8K2.u10967 = [384126823169, 1999834312676, 3242574521138, 1412078970394, 78538688733, 0, 0, 0] := by
  rw [show D2M8K2.u10967 = KTree.node D2M8K2.u10963 (nat_lit 23925972) (nat_lit 3256651690) (nat_lit 0) D2M8K2.u10966 from rfl, totK_node, atot10963, atot10966]
  decide +kernel

theorem arows10976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10976 = true := by
  rw [show D2M8K2.u10976 = KTree.node D2M8K2.u10972 (nat_lit 23976480) (nat_lit 2262957951) (nat_lit 0) D2M8K2.u10975 from rfl, allE_node, arows10972, irow10976, arows10975]
  all_goals rfl

theorem atot10976 : totK PD2M8K2 D2M8K2.u10976 = [803340530019, 2918407567712, 2834805981216, 679240799829, 33612805224, 0, 0, 0] := by
  rw [show D2M8K2.u10976 = KTree.node D2M8K2.u10972 (nat_lit 23976480) (nat_lit 2262957951) (nat_lit 0) D2M8K2.u10975 from rfl, totK_node, atot10972, atot10975]
  decide +kernel

theorem arows10983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10983 = true := by
  rw [show D2M8K2.u10983 = KTree.node D2M8K2.u10979 (nat_lit 23986369) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u10982 from rfl, allE_node, arows10979, irow10983, arows10982]
  all_goals rfl

theorem atot10983 : totK PD2M8K2 D2M8K2.u10983 = [795277310230, 2910352905095, 2878367149011, 594570874074, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u10983 = KTree.node D2M8K2.u10979 (nat_lit 23986369) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u10982 from rfl, totK_node, atot10979, atot10982]
  decide +kernel

theorem arows10991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10991 = true := by
  rw [show D2M8K2.u10991 = KTree.node D2M8K2.u10987 (nat_lit 23993366) (nat_lit 914415284) (nat_lit 0) D2M8K2.u10990 from rfl, allE_node, arows10987, irow10991, arows10990]
  all_goals rfl

theorem atot10991 : totK PD2M8K2 D2M8K2.u10991 = [0, 1250478480166, 3541869549847, 2121488455476, 200518915895, 1206465782, 0, 0] := by
  rw [show D2M8K2.u10991 = KTree.node D2M8K2.u10987 (nat_lit 23993366) (nat_lit 914415284) (nat_lit 0) D2M8K2.u10990 from rfl, totK_node, atot10987, atot10990]
  decide +kernel

theorem arows10998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10998 = true := by
  rw [show D2M8K2.u10998 = KTree.node D2M8K2.u10994 (nat_lit 24005920) (nat_lit 3287993885) (nat_lit 0) D2M8K2.u10997 from rfl, allE_node, arows10994, irow10998, arows10997]
  all_goals rfl

theorem atot10998 : totK PD2M8K2 D2M8K2.u10998 = [0, 877420547608, 3050371843660, 2604614505010, 488553999341, 17590593026, 0, 0] := by
  rw [show D2M8K2.u10998 = KTree.node D2M8K2.u10994 (nat_lit 24005920) (nat_lit 3287993885) (nat_lit 0) D2M8K2.u10997 from rfl, totK_node, atot10994, atot10997]
  decide +kernel

theorem arows11010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11010 = true := by
  rw [show D2M8K2.u11010 = KTree.node D2M8K2.u11006 (nat_lit 24014959) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u11009 from rfl, allE_node, arows11006, irow11010, arows11009]
  all_goals rfl

theorem atot11010 : totK PD2M8K2 D2M8K2.u11010 = [750137227213, 2763966402126, 2854254819488, 815790117806, 50403481926, 0, 0, 0] := by
  rw [show D2M8K2.u11010 = KTree.node D2M8K2.u11006 (nat_lit 24014959) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u11009 from rfl, totK_node, atot11006, atot11009]
  decide +kernel

theorem arows11017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11017 = true := by
  rw [show D2M8K2.u11017 = KTree.node D2M8K2.u11013 (nat_lit 24025585) (nat_lit 1364756658) (nat_lit 0) D2M8K2.u11016 from rfl, allE_node, arows11013, irow11017, arows11016]
  all_goals rfl

theorem atot11017 : totK PD2M8K2 D2M8K2.u11017 = [849903555346, 2979011167029, 2796629145953, 586558120235, 19905831458, 0, 0, 0] := by
  rw [show D2M8K2.u11017 = KTree.node D2M8K2.u11013 (nat_lit 24025585) (nat_lit 1364756658) (nat_lit 0) D2M8K2.u11016 from rfl, totK_node, atot11013, atot11016]
  decide +kernel

theorem arows11025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11025 = true := by
  rw [show D2M8K2.u11025 = KTree.node D2M8K2.u11021 (nat_lit 24032744) (nat_lit 2298548100) (nat_lit 0) D2M8K2.u11024 from rfl, allE_node, arows11021, irow11025, arows11024]
  all_goals rfl

theorem atot11025 : totK PD2M8K2 D2M8K2.u11025 = [383209705629, 1860769314770, 3098275484461, 1595607325477, 144187927769, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11025 = KTree.node D2M8K2.u11021 (nat_lit 24032744) (nat_lit 2298548100) (nat_lit 0) D2M8K2.u11024 from rfl, totK_node, atot11021, atot11024]
  decide +kernel

theorem arows11032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11032 = true := by
  rw [show D2M8K2.u11032 = KTree.node D2M8K2.u11028 (nat_lit 24044926) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u11031 from rfl, allE_node, arows11028, irow11032, arows11031]
  all_goals rfl

theorem atot11032 : totK PD2M8K2 D2M8K2.u11032 = [0, 1141732075976, 3295292750925, 2344263077012, 388897990584, 13105450397, 0, 0] := by
  rw [show D2M8K2.u11032 = KTree.node D2M8K2.u11028 (nat_lit 24044926) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u11031 from rfl, totK_node, atot11028, atot11031]
  decide +kernel

theorem arows11041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11041 = true := by
  rw [show D2M8K2.u11041 = KTree.node D2M8K2.u11037 (nat_lit 24053817) (nat_lit 1822536073) (nat_lit 0) D2M8K2.u11040 from rfl, allE_node, arows11037, irow11041, arows11040]
  all_goals rfl

theorem atot11041 : totK PD2M8K2 D2M8K2.u11041 = [511182402710, 2075825251589, 2842109398237, 1502981923193, 206537702602, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11041 = KTree.node D2M8K2.u11037 (nat_lit 24053817) (nat_lit 1822536073) (nat_lit 0) D2M8K2.u11040 from rfl, totK_node, atot11037, atot11040]
  decide +kernel

theorem arows11048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11048 = true := by
  rw [show D2M8K2.u11048 = KTree.node D2M8K2.u11044 (nat_lit 24061051) (nat_lit 2154437194) (nat_lit 0) D2M8K2.u11047 from rfl, allE_node, arows11044, irow11048, arows11047]
  all_goals rfl

theorem atot11048 : totK PD2M8K2 D2M8K2.u11048 = [772678072191, 2773383621447, 2837288054923, 801635266612, 43718703500, 0, 0, 0] := by
  rw [show D2M8K2.u11048 = KTree.node D2M8K2.u11044 (nat_lit 24061051) (nat_lit 2154437194) (nat_lit 0) D2M8K2.u11047 from rfl, totK_node, atot11044, atot11047]
  decide +kernel

theorem arows11056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11056 = true := by
  rw [show D2M8K2.u11056 = KTree.node D2M8K2.u11052 (nat_lit 24067830) (nat_lit 3703400203) (nat_lit 0) D2M8K2.u11055 from rfl, allE_node, arows11052, irow11056, arows11055]
  all_goals rfl

theorem atot11056 : totK PD2M8K2 D2M8K2.u11056 = [742679185588, 2862186393892, 2953920724501, 650074602839, 19601020673, 0, 0, 0] := by
  rw [show D2M8K2.u11056 = KTree.node D2M8K2.u11052 (nat_lit 24067830) (nat_lit 3703400203) (nat_lit 0) D2M8K2.u11055 from rfl, totK_node, atot11052, atot11055]
  decide +kernel

theorem arows11063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11063 = true := by
  rw [show D2M8K2.u11063 = KTree.node D2M8K2.u11059 (nat_lit 24078776) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u11062 from rfl, allE_node, arows11059, irow11063, arows11062]
  all_goals rfl

theorem atot11063 : totK PD2M8K2 D2M8K2.u11063 = [0, 1249561327758, 3605797702013, 2092823819177, 185808331120, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11063 = KTree.node D2M8K2.u11059 (nat_lit 24078776) (nat_lit 3865940388) (nat_lit 0) D2M8K2.u11062 from rfl, totK_node, atot11059, atot11062]
  decide +kernel

theorem arows11073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11073 = true := by
  rw [show D2M8K2.u11073 = KTree.node D2M8K2.u11069 (nat_lit 24090197) (nat_lit 1988992452) (nat_lit 0) D2M8K2.u11072 from rfl, allE_node, arows11069, irow11073, arows11072]
  all_goals rfl

theorem atot11073 : totK PD2M8K2 D2M8K2.u11073 = [421327836975, 1847240715764, 2901758036371, 1705419144888, 243771012546, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11073 = KTree.node D2M8K2.u11069 (nat_lit 24090197) (nat_lit 1988992452) (nat_lit 0) D2M8K2.u11072 from rfl, totK_node, atot11069, atot11072]
  decide +kernel

theorem arows11080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11080 = true := by
  rw [show D2M8K2.u11080 = KTree.node D2M8K2.u11076 (nat_lit 24104489) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u11079 from rfl, allE_node, arows11076, irow11080, arows11079]
  all_goals rfl

theorem atot11080 : totK PD2M8K2 D2M8K2.u11080 = [802854010321, 2973232929086, 2866872505365, 548975523133, 14241856732, 0, 0, 0] := by
  rw [show D2M8K2.u11080 = KTree.node D2M8K2.u11076 (nat_lit 24104489) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u11079 from rfl, totK_node, atot11076, atot11079]
  decide +kernel

theorem arows11088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11088 = true := by
  rw [show D2M8K2.u11088 = KTree.node D2M8K2.u11084 (nat_lit 24114620) (nat_lit 2592936956) (nat_lit 0) D2M8K2.u11087 from rfl, allE_node, arows11084, irow11088, arows11087]
  all_goals rfl

theorem atot11088 : totK PD2M8K2 D2M8K2.u11088 = [427832996020, 2151911236908, 3235796192715, 1276554414775, 74650934376, 0, 0, 0] := by
  rw [show D2M8K2.u11088 = KTree.node D2M8K2.u11084 (nat_lit 24114620) (nat_lit 2592936956) (nat_lit 0) D2M8K2.u11087 from rfl, totK_node, atot11084, atot11087]
  decide +kernel

theorem arows11095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11095 = true := by
  rw [show D2M8K2.u11095 = KTree.node D2M8K2.u11091 (nat_lit 24125222) (nat_lit 3883806512) (nat_lit 0) D2M8K2.u11094 from rfl, allE_node, arows11091, irow11095, arows11094]
  all_goals rfl

theorem atot11095 : totK PD2M8K2 D2M8K2.u11095 = [0, 799615237476, 2993298052683, 2831457267053, 467232505666, 8351110384, 0, 0] := by
  rw [show D2M8K2.u11095 = KTree.node D2M8K2.u11091 (nat_lit 24125222) (nat_lit 3883806512) (nat_lit 0) D2M8K2.u11094 from rfl, totK_node, atot11091, atot11094]
  decide +kernel

theorem arows11104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11104 = true := by
  rw [show D2M8K2.u11104 = KTree.node D2M8K2.u11100 (nat_lit 24135872) (nat_lit 2679106378) (nat_lit 0) D2M8K2.u11103 from rfl, allE_node, arows11100, irow11104, arows11103]
  all_goals rfl

theorem atot11104 : totK PD2M8K2 D2M8K2.u11104 = [0, 867310257074, 2979947665003, 2684921444217, 592662196628, 24810199646, 0, 0] := by
  rw [show D2M8K2.u11104 = KTree.node D2M8K2.u11100 (nat_lit 24135872) (nat_lit 2679106378) (nat_lit 0) D2M8K2.u11103 from rfl, totK_node, atot11100, atot11103]
  decide +kernel

theorem arows11111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11111 = true := by
  rw [show D2M8K2.u11111 = KTree.node D2M8K2.u11107 (nat_lit 24146113) (nat_lit 1414861519) (nat_lit 0) D2M8K2.u11110 from rfl, allE_node, arows11107, irow11111, arows11110]
  all_goals rfl

theorem atot11111 : totK PD2M8K2 D2M8K2.u11111 = [0, 828900745369, 3011464643709, 2798568646420, 469273193553, 14089731401, 0, 0] := by
  rw [show D2M8K2.u11111 = KTree.node D2M8K2.u11107 (nat_lit 24146113) (nat_lit 1414861519) (nat_lit 0) D2M8K2.u11110 from rfl, totK_node, atot11107, atot11110]
  decide +kernel

theorem arows11119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11119 = true := by
  rw [show D2M8K2.u11119 = KTree.node D2M8K2.u11115 (nat_lit 24152949) (nat_lit 1734682400) (nat_lit 0) D2M8K2.u11118 from rfl, allE_node, arows11115, irow11119, arows11118]
  all_goals rfl

theorem atot11119 : totK PD2M8K2 D2M8K2.u11119 = [0, 816078251927, 2884076519405, 2781431414250, 565978758356, 21757392647, 0, 0] := by
  rw [show D2M8K2.u11119 = KTree.node D2M8K2.u11115 (nat_lit 24152949) (nat_lit 1734682400) (nat_lit 0) D2M8K2.u11118 from rfl, totK_node, atot11115, atot11118]
  decide +kernel

theorem arows11126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11126 = true := by
  rw [show D2M8K2.u11126 = KTree.node D2M8K2.u11122 (nat_lit 24160038) (nat_lit 3863471170) (nat_lit 0) D2M8K2.u11125 from rfl, allE_node, arows11122, irow11126, arows11125]
  all_goals rfl

theorem atot11126 : totK PD2M8K2 D2M8K2.u11126 = [0, 0, 1305627225415, 3536198909254, 1924740921878, 213253333326, 1369150432, 0] := by
  rw [show D2M8K2.u11126 = KTree.node D2M8K2.u11122 (nat_lit 24160038) (nat_lit 3863471170) (nat_lit 0) D2M8K2.u11125 from rfl, totK_node, atot11122, atot11125]
  decide +kernel

theorem arows11137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11137 = true := by
  rw [show D2M8K2.u11137 = KTree.node D2M8K2.u11133 (nat_lit 24175688) (nat_lit 3439126620) (nat_lit 0) D2M8K2.u11136 from rfl, allE_node, arows11133, irow11137, arows11136]
  all_goals rfl

theorem atot11137 : totK PD2M8K2 D2M8K2.u11137 = [0, 417485306014, 2238276840425, 3260902746868, 1066119849738, 58082255293, 0, 0] := by
  rw [show D2M8K2.u11137 = KTree.node D2M8K2.u11133 (nat_lit 24175688) (nat_lit 3439126620) (nat_lit 0) D2M8K2.u11136 from rfl, totK_node, atot11133, atot11136]
  decide +kernel

theorem arows11144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11144 = true := by
  rw [show D2M8K2.u11144 = KTree.node D2M8K2.u11140 (nat_lit 24226724) (nat_lit 2768950402) (nat_lit 0) D2M8K2.u11143 from rfl, allE_node, arows11140, irow11144, arows11143]
  all_goals rfl

theorem atot11144 : totK PD2M8K2 D2M8K2.u11144 = [0, 789286550296, 2916608669219, 2922309797529, 600817462744, 18334076299, 0, 0] := by
  rw [show D2M8K2.u11144 = KTree.node D2M8K2.u11140 (nat_lit 24226724) (nat_lit 2768950402) (nat_lit 0) D2M8K2.u11143 from rfl, totK_node, atot11140, atot11143]
  decide +kernel

theorem arows11152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11152 = true := by
  rw [show D2M8K2.u11152 = KTree.node D2M8K2.u11148 (nat_lit 24237065) (nat_lit 1629770820) (nat_lit 0) D2M8K2.u11151 from rfl, allE_node, arows11148, irow11152, arows11151]
  all_goals rfl

theorem atot11152 : totK PD2M8K2 D2M8K2.u11152 = [0, 862591457869, 2980644020721, 2761952618146, 555225331672, 18601571664, 0, 0] := by
  rw [show D2M8K2.u11152 = KTree.node D2M8K2.u11148 (nat_lit 24237065) (nat_lit 1629770820) (nat_lit 0) D2M8K2.u11151 from rfl, totK_node, atot11148, atot11151]
  decide +kernel

theorem arows11159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11159 = true := by
  rw [show D2M8K2.u11159 = KTree.node D2M8K2.u11155 (nat_lit 24265519) (nat_lit 2447849823) (nat_lit 0) D2M8K2.u11158 from rfl, allE_node, arows11155, irow11159, arows11158]
  all_goals rfl

theorem atot11159 : totK PD2M8K2 D2M8K2.u11159 = [0, 932316840652, 3140052737662, 2710429331620, 450362552811, 6717958024, 0, 0] := by
  rw [show D2M8K2.u11159 = KTree.node D2M8K2.u11155 (nat_lit 24265519) (nat_lit 2447849823) (nat_lit 0) D2M8K2.u11158 from rfl, totK_node, atot11155, atot11158]
  decide +kernel

theorem arows11168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11168 = true := by
  rw [show D2M8K2.u11168 = KTree.node D2M8K2.u11164 (nat_lit 24275694) (nat_lit 2717394506) (nat_lit 0) D2M8K2.u11167 from rfl, allE_node, arows11164, irow11168, arows11167]
  all_goals rfl

theorem atot11168 : totK PD2M8K2 D2M8K2.u11168 = [0, 865793683135, 2969890839131, 2775805437728, 553064845527, 18088360733, 0, 0] := by
  rw [show D2M8K2.u11168 = KTree.node D2M8K2.u11164 (nat_lit 24275694) (nat_lit 2717394506) (nat_lit 0) D2M8K2.u11167 from rfl, totK_node, atot11164, atot11167]
  decide +kernel

theorem arows11175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11175 = true := by
  rw [show D2M8K2.u11175 = KTree.node D2M8K2.u11171 (nat_lit 24303792) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u11174 from rfl, allE_node, arows11171, irow11175, arows11174]
  all_goals rfl

theorem atot11175 : totK PD2M8K2 D2M8K2.u11175 = [0, 854249659819, 3013261142441, 2771538682675, 524500966767, 15083816312, 0, 0] := by
  rw [show D2M8K2.u11175 = KTree.node D2M8K2.u11171 (nat_lit 24303792) (nat_lit 3539834764) (nat_lit 0) D2M8K2.u11174 from rfl, totK_node, atot11171, atot11174]
  decide +kernel

theorem arows11183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11183 = true := by
  rw [show D2M8K2.u11183 = KTree.node D2M8K2.u11179 (nat_lit 24311506) (nat_lit 3683838795) (nat_lit 0) D2M8K2.u11182 from rfl, allE_node, arows11179, irow11183, arows11182]
  all_goals rfl

theorem atot11183 : totK PD2M8K2 D2M8K2.u11183 = [0, 822264599616, 2996313954360, 2817990808437, 534539708751, 15591084001, 0, 0] := by
  rw [show D2M8K2.u11183 = KTree.node D2M8K2.u11179 (nat_lit 24311506) (nat_lit 3683838795) (nat_lit 0) D2M8K2.u11182 from rfl, totK_node, atot11179, atot11182]
  decide +kernel

theorem arows11190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11190 = true := by
  rw [show D2M8K2.u11190 = KTree.node D2M8K2.u11186 (nat_lit 24318264) (nat_lit 3578685551) (nat_lit 0) D2M8K2.u11189 from rfl, allE_node, arows11186, irow11190, arows11189]
  all_goals rfl

theorem atot11190 : totK PD2M8K2 D2M8K2.u11190 = [0, 857802487198, 3031523040055, 2770243186231, 514046487864, 16966758967, 0, 0] := by
  rw [show D2M8K2.u11190 = KTree.node D2M8K2.u11186 (nat_lit 24318264) (nat_lit 3578685551) (nat_lit 0) D2M8K2.u11189 from rfl, totK_node, atot11186, atot11189]
  decide +kernel

theorem arows11200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11200 = true := by
  rw [show D2M8K2.u11200 = KTree.node D2M8K2.u11196 (nat_lit 24353287) (nat_lit 1475285690) (nat_lit 0) D2M8K2.u11199 from rfl, allE_node, arows11196, irow11200, arows11199]
  all_goals rfl

theorem atot11200 : totK PD2M8K2 D2M8K2.u11200 = [0, 800666043877, 3010680590128, 2888953577225, 501743438240, 7670123334, 0, 0] := by
  rw [show D2M8K2.u11200 = KTree.node D2M8K2.u11196 (nat_lit 24353287) (nat_lit 1475285690) (nat_lit 0) D2M8K2.u11199 from rfl, totK_node, atot11196, atot11199]
  decide +kernel

theorem arows11207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11207 = true := by
  rw [show D2M8K2.u11207 = KTree.node D2M8K2.u11203 (nat_lit 24363793) (nat_lit 1483022133) (nat_lit 0) D2M8K2.u11206 from rfl, allE_node, arows11203, irow11207, arows11206]
  all_goals rfl

theorem atot11207 : totK PD2M8K2 D2M8K2.u11207 = [449419051412, 1675520092955, 2509215717177, 2060249814741, 553135288542, 25928157475, 0, 0] := by
  rw [show D2M8K2.u11207 = KTree.node D2M8K2.u11203 (nat_lit 24363793) (nat_lit 1483022133) (nat_lit 0) D2M8K2.u11206 from rfl, totK_node, atot11203, atot11206]
  decide +kernel

theorem arows11215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11215 = true := by
  rw [show D2M8K2.u11215 = KTree.node D2M8K2.u11211 (nat_lit 24435420) (nat_lit 3129697929) (nat_lit 0) D2M8K2.u11214 from rfl, allE_node, arows11211, irow11215, arows11214]
  all_goals rfl

theorem atot11215 : totK PD2M8K2 D2M8K2.u11215 = [757388312352, 2707072620190, 2862400643361, 861291327731, 40160714361, 0, 0, 0] := by
  rw [show D2M8K2.u11215 = KTree.node D2M8K2.u11211 (nat_lit 24435420) (nat_lit 3129697929) (nat_lit 0) D2M8K2.u11214 from rfl, totK_node, atot11211, atot11214]
  decide +kernel

theorem arows11222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11222 = true := by
  rw [show D2M8K2.u11222 = KTree.node D2M8K2.u11218 (nat_lit 24441869) (nat_lit 1644716157) (nat_lit 0) D2M8K2.u11221 from rfl, allE_node, arows11218, irow11222, arows11221]
  all_goals rfl

theorem atot11222 : totK PD2M8K2 D2M8K2.u11222 = [835130158003, 2960524198952, 2824475384728, 586598749924, 18153851709, 0, 0, 0] := by
  rw [show D2M8K2.u11222 = KTree.node D2M8K2.u11218 (nat_lit 24441869) (nat_lit 1644716157) (nat_lit 0) D2M8K2.u11221 from rfl, totK_node, atot11218, atot11221]
  decide +kernel

theorem arows11231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11231 = true := by
  rw [show D2M8K2.u11231 = KTree.node D2M8K2.u11227 (nat_lit 24452372) (nat_lit 3262189551) (nat_lit 0) D2M8K2.u11230 from rfl, allE_node, arows11227, irow11231, arows11230]
  all_goals rfl

theorem atot11231 : totK PD2M8K2 D2M8K2.u11231 = [75805549015, 1231292065463, 3016294877345, 2270486531741, 613257309253, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11231 = KTree.node D2M8K2.u11227 (nat_lit 24452372) (nat_lit 3262189551) (nat_lit 0) D2M8K2.u11230 from rfl, totK_node, atot11227, atot11230]
  decide +kernel

theorem arows11238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11238 = true := by
  rw [show D2M8K2.u11238 = KTree.node D2M8K2.u11234 (nat_lit 24458671) (nat_lit 2225277628) (nat_lit 0) D2M8K2.u11237 from rfl, allE_node, arows11234, irow11238, arows11237]
  all_goals rfl

theorem atot11238 : totK PD2M8K2 D2M8K2.u11238 = [0, 871436172596, 3039661901466, 2766463879459, 503298198319, 10378741320, 0, 0] := by
  rw [show D2M8K2.u11238 = KTree.node D2M8K2.u11234 (nat_lit 24458671) (nat_lit 2225277628) (nat_lit 0) D2M8K2.u11237 from rfl, totK_node, atot11234, atot11237]
  decide +kernel

theorem arows11246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11246 = true := by
  rw [show D2M8K2.u11246 = KTree.node D2M8K2.u11242 (nat_lit 24465864) (nat_lit 3296864284) (nat_lit 0) D2M8K2.u11245 from rfl, allE_node, arows11242, irow11246, arows11245]
  all_goals rfl

theorem atot11246 : totK PD2M8K2 D2M8K2.u11246 = [256161886194, 1266331192803, 2746709175064, 2439908987060, 475787217003, 10717512769, 0, 0] := by
  rw [show D2M8K2.u11246 = KTree.node D2M8K2.u11242 (nat_lit 24465864) (nat_lit 3296864284) (nat_lit 0) D2M8K2.u11245 from rfl, totK_node, atot11242, atot11245]
  decide +kernel

theorem arows11253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11253 = true := by
  rw [show D2M8K2.u11253 = KTree.node D2M8K2.u11249 (nat_lit 24473663) (nat_lit 2759702198) (nat_lit 0) D2M8K2.u11252 from rfl, allE_node, arows11249, irow11253, arows11252]
  all_goals rfl

theorem atot11253 : totK PD2M8K2 D2M8K2.u11253 = [830607270059, 2832848294724, 2802499336889, 775429421079, 38966267249, 0, 0, 0] := by
  rw [show D2M8K2.u11253 = KTree.node D2M8K2.u11249 (nat_lit 24473663) (nat_lit 2759702198) (nat_lit 0) D2M8K2.u11252 from rfl, totK_node, atot11249, atot11252]
  decide +kernel

theorem arows11267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11267 = true := by
  rw [show D2M8K2.u11267 = KTree.node D2M8K2.u11263 (nat_lit 24483141) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u11266 from rfl, allE_node, arows11263, irow11267, arows11266]
  all_goals rfl

theorem atot11267 : totK PD2M8K2 D2M8K2.u11267 = [811866963684, 2953510816895, 2855055996116, 586325428674, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u11267 = KTree.node D2M8K2.u11263 (nat_lit 24483141) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u11266 from rfl, totK_node, atot11263, atot11266]
  decide +kernel

theorem arows11274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11274 = true := by
  rw [show D2M8K2.u11274 = KTree.node D2M8K2.u11270 (nat_lit 24490725) (nat_lit 1375939068) (nat_lit 0) D2M8K2.u11273 from rfl, allE_node, arows11270, irow11274, arows11273]
  all_goals rfl

theorem atot11274 : totK PD2M8K2 D2M8K2.u11274 = [90490504222, 1492752317306, 3447684310972, 1929335862623, 186185077185, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11274 = KTree.node D2M8K2.u11270 (nat_lit 24490725) (nat_lit 1375939068) (nat_lit 0) D2M8K2.u11273 from rfl, totK_node, atot11270, atot11273]
  decide +kernel

theorem arows11282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11282 = true := by
  rw [show D2M8K2.u11282 = KTree.node D2M8K2.u11278 (nat_lit 24503126) (nat_lit 2237915865) (nat_lit 0) D2M8K2.u11281 from rfl, allE_node, arows11278, irow11282, arows11281]
  all_goals rfl

theorem atot11282 : totK PD2M8K2 D2M8K2.u11282 = [0, 891447653489, 3093027336343, 2595352035136, 483523831705, 17590593026, 0, 0] := by
  rw [show D2M8K2.u11282 = KTree.node D2M8K2.u11278 (nat_lit 24503126) (nat_lit 2237915865) (nat_lit 0) D2M8K2.u11281 from rfl, totK_node, atot11278, atot11281]
  decide +kernel

theorem arows11289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11289 = true := by
  rw [show D2M8K2.u11289 = KTree.node D2M8K2.u11285 (nat_lit 24512652) (nat_lit 3130586911) (nat_lit 0) D2M8K2.u11288 from rfl, allE_node, arows11285, irow11289, arows11288]
  all_goals rfl

theorem atot11289 : totK PD2M8K2 D2M8K2.u11289 = [753971791401, 2714312306566, 2815621231685, 921596166819, 68351188370, 0, 0, 0] := by
  rw [show D2M8K2.u11289 = KTree.node D2M8K2.u11285 (nat_lit 24512652) (nat_lit 3130586911) (nat_lit 0) D2M8K2.u11288 from rfl, totK_node, atot11285, atot11288]
  decide +kernel

theorem arows11298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11298 = true := by
  rw [show D2M8K2.u11298 = KTree.node D2M8K2.u11294 (nat_lit 24522266) (nat_lit 3309332710) (nat_lit 0) D2M8K2.u11297 from rfl, allE_node, arows11294, irow11298, arows11297]
  all_goals rfl

theorem atot11298 : totK PD2M8K2 D2M8K2.u11298 = [852492062124, 2893102209743, 2765466105516, 690257753173, 25481086211, 0, 0, 0] := by
  rw [show D2M8K2.u11298 = KTree.node D2M8K2.u11294 (nat_lit 24522266) (nat_lit 3309332710) (nat_lit 0) D2M8K2.u11297 from rfl, totK_node, atot11294, atot11297]
  decide +kernel

theorem arows11305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11305 = true := by
  rw [show D2M8K2.u11305 = KTree.node D2M8K2.u11301 (nat_lit 24529308) (nat_lit 1526857381) (nat_lit 0) D2M8K2.u11304 from rfl, allE_node, arows11301, irow11305, arows11304]
  all_goals rfl

theorem atot11305 : totK PD2M8K2 D2M8K2.u11305 = [386732656573, 2058640892932, 3208616931437, 1389806065255, 127495519146, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11305 = KTree.node D2M8K2.u11301 (nat_lit 24529308) (nat_lit 1526857381) (nat_lit 0) D2M8K2.u11304 from rfl, totK_node, atot11301, atot11304]
  decide +kernel

theorem arows11313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11313 = true := by
  rw [show D2M8K2.u11313 = KTree.node D2M8K2.u11309 (nat_lit 24542148) (nat_lit 3059626523) (nat_lit 0) D2M8K2.u11312 from rfl, allE_node, arows11309, irow11313, arows11312]
  all_goals rfl

theorem atot11313 : totK PD2M8K2 D2M8K2.u11313 = [0, 1098407742411, 3281586054214, 2407082043207, 394619476232, 13105450397, 0, 0] := by
  rw [show D2M8K2.u11313 = KTree.node D2M8K2.u11309 (nat_lit 24542148) (nat_lit 3059626523) (nat_lit 0) D2M8K2.u11312 from rfl, totK_node, atot11309, atot11312]
  decide +kernel

theorem arows11320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11320 = true := by
  rw [show D2M8K2.u11320 = KTree.node D2M8K2.u11316 (nat_lit 24549004) (nat_lit 3074038853) (nat_lit 0) D2M8K2.u11319 from rfl, allE_node, arows11316, irow11320, arows11319]
  all_goals rfl

theorem atot11320 : totK PD2M8K2 D2M8K2.u11320 = [433967504439, 1937060962385, 2941238547628, 1646869250885, 217391700625, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11320 = KTree.node D2M8K2.u11316 (nat_lit 24549004) (nat_lit 3074038853) (nat_lit 0) D2M8K2.u11319 from rfl, totK_node, atot11316, atot11319]
  decide +kernel

theorem arows11330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11330 = true := by
  rw [show D2M8K2.u11330 = KTree.node D2M8K2.u11326 (nat_lit 24558076) (nat_lit 3850501190) (nat_lit 0) D2M8K2.u11329 from rfl, allE_node, arows11326, irow11330, arows11329]
  all_goals rfl

theorem atot11330 : totK PD2M8K2 D2M8K2.u11330 = [750508464682, 2734072574915, 2858167025153, 854014024297, 47189421326, 0, 0, 0] := by
  rw [show D2M8K2.u11330 = KTree.node D2M8K2.u11326 (nat_lit 24558076) (nat_lit 3850501190) (nat_lit 0) D2M8K2.u11329 from rfl, totK_node, atot11326, atot11329]
  decide +kernel

theorem arows11337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11337 = true := by
  rw [show D2M8K2.u11337 = KTree.node D2M8K2.u11333 (nat_lit 24564692) (nat_lit 3258713885) (nat_lit 0) D2M8K2.u11336 from rfl, allE_node, arows11333, irow11337, arows11336]
  all_goals rfl

theorem atot11337 : totK PD2M8K2 D2M8K2.u11337 = [853715516480, 2986704257578, 2789188224257, 576579527791, 17809204495, 0, 0, 0] := by
  rw [show D2M8K2.u11337 = KTree.node D2M8K2.u11333 (nat_lit 24564692) (nat_lit 3258713885) (nat_lit 0) D2M8K2.u11336 from rfl, totK_node, atot11333, atot11336]
  decide +kernel

theorem arows11345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11345 = true := by
  rw [show D2M8K2.u11345 = KTree.node D2M8K2.u11341 (nat_lit 24576152) (nat_lit 3886635249) (nat_lit 0) D2M8K2.u11344 from rfl, allE_node, arows11341, irow11345, arows11344]
  all_goals rfl

theorem atot11345 : totK PD2M8K2 D2M8K2.u11345 = [0, 1324823005880, 3621669968156, 2041982175903, 183291037027, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11345 = KTree.node D2M8K2.u11341 (nat_lit 24576152) (nat_lit 3886635249) (nat_lit 0) D2M8K2.u11344 from rfl, totK_node, atot11341, atot11344]
  decide +kernel

theorem arows11352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11352 = true := by
  rw [show D2M8K2.u11352 = KTree.node D2M8K2.u11348 (nat_lit 24586997) (nat_lit 1061053549) (nat_lit 0) D2M8K2.u11351 from rfl, allE_node, arows11348, irow11352, arows11351]
  all_goals rfl

theorem atot11352 : totK PD2M8K2 D2M8K2.u11352 = [340079057287, 1660381658397, 3059705838504, 1866620480045, 254556259500, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11352 = KTree.node D2M8K2.u11348 (nat_lit 24586997) (nat_lit 1061053549) (nat_lit 0) D2M8K2.u11351 from rfl, totK_node, atot11348, atot11351]
  decide +kernel

theorem arows11361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11361 = true := by
  rw [show D2M8K2.u11361 = KTree.node D2M8K2.u11357 (nat_lit 24600444) (nat_lit 3226978531) (nat_lit 0) D2M8K2.u11360 from rfl, allE_node, arows11357, irow11361, arows11360]
  all_goals rfl

theorem atot11361 : totK PD2M8K2 D2M8K2.u11361 = [704812493099, 2653438388100, 2942464723929, 917887071016, 50600352594, 0, 0, 0] := by
  rw [show D2M8K2.u11361 = KTree.node D2M8K2.u11357 (nat_lit 24600444) (nat_lit 3226978531) (nat_lit 0) D2M8K2.u11360 from rfl, totK_node, atot11357, atot11360]
  decide +kernel

theorem arows11368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11368 = true := by
  rw [show D2M8K2.u11368 = KTree.node D2M8K2.u11364 (nat_lit 24610821) (nat_lit 1471173990) (nat_lit 0) D2M8K2.u11367 from rfl, allE_node, arows11364, irow11368, arows11367]
  all_goals rfl

theorem atot11368 : totK PD2M8K2 D2M8K2.u11368 = [618028270821, 2594016955256, 3037809930586, 933928417767, 57184363814, 0, 0, 0] := by
  rw [show D2M8K2.u11368 = KTree.node D2M8K2.u11364 (nat_lit 24610821) (nat_lit 1471173990) (nat_lit 0) D2M8K2.u11367 from rfl, totK_node, atot11364, atot11367]
  decide +kernel

theorem arows11376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11376 = true := by
  rw [show D2M8K2.u11376 = KTree.node D2M8K2.u11372 (nat_lit 24622262) (nat_lit 3179939393) (nat_lit 0) D2M8K2.u11375 from rfl, allE_node, arows11372, irow11376, arows11375]
  all_goals rfl

theorem atot11376 : totK PD2M8K2 D2M8K2.u11376 = [0, 1118390725067, 3348567131620, 2393794866984, 326576322266, 5986997553, 0, 0] := by
  rw [show D2M8K2.u11376 = KTree.node D2M8K2.u11372 (nat_lit 24622262) (nat_lit 3179939393) (nat_lit 0) D2M8K2.u11375 from rfl, totK_node, atot11372, atot11375]
  decide +kernel

theorem arows11383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11383 = true := by
  rw [show D2M8K2.u11383 = KTree.node D2M8K2.u11379 (nat_lit 24633032) (nat_lit 2924018580) (nat_lit 0) D2M8K2.u11382 from rfl, allE_node, arows11379, irow11383, arows11382]
  all_goals rfl

theorem atot11383 : totK PD2M8K2 D2M8K2.u11383 = [0, 877079160030, 3012124189274, 2708724290428, 592720139532, 25575415551, 0, 0] := by
  rw [show D2M8K2.u11383 = KTree.node D2M8K2.u11379 (nat_lit 24633032) (nat_lit 2924018580) (nat_lit 0) D2M8K2.u11382 from rfl, totK_node, atot11379, atot11382]
  decide +kernel

theorem arows11394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11394 = true := by
  rw [show D2M8K2.u11394 = KTree.node D2M8K2.u11390 (nat_lit 24684064) (nat_lit 2356958597) (nat_lit 0) D2M8K2.u11393 from rfl, allE_node, arows11390, irow11394, arows11393]
  all_goals rfl

theorem atot11394 : totK PD2M8K2 D2M8K2.u11394 = [0, 735780184590, 2658437251024, 2900126163470, 893736506156, 46315814054, 0, 0] := by
  rw [show D2M8K2.u11394 = KTree.node D2M8K2.u11390 (nat_lit 24684064) (nat_lit 2356958597) (nat_lit 0) D2M8K2.u11393 from rfl, totK_node, atot11390, atot11393]
  decide +kernel

theorem arows11401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11401 = true := by
  rw [show D2M8K2.u11401 = KTree.node D2M8K2.u11397 (nat_lit 24690574) (nat_lit 3694129382) (nat_lit 0) D2M8K2.u11400 from rfl, allE_node, arows11397, irow11401, arows11400]
  all_goals rfl

theorem atot11401 : totK PD2M8K2 D2M8K2.u11401 = [0, 840688531904, 2996181860823, 2799199695936, 553634080791, 11323144342, 0, 0] := by
  rw [show D2M8K2.u11401 = KTree.node D2M8K2.u11397 (nat_lit 24690574) (nat_lit 3694129382) (nat_lit 0) D2M8K2.u11400 from rfl, totK_node, atot11397, atot11400]
  decide +kernel

theorem arows11409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11409 = true := by
  rw [show D2M8K2.u11409 = KTree.node D2M8K2.u11405 (nat_lit 24701070) (nat_lit 3950856744) (nat_lit 0) D2M8K2.u11408 from rfl, allE_node, arows11405, irow11409, arows11408]
  all_goals rfl

theorem atot11409 : totK PD2M8K2 D2M8K2.u11409 = [0, 91855302876, 1306887664561, 2997603323780, 2173406048890, 592802161675, 36921873854, 0] := by
  rw [show D2M8K2.u11409 = KTree.node D2M8K2.u11405 (nat_lit 24701070) (nat_lit 3950856744) (nat_lit 0) D2M8K2.u11408 from rfl, totK_node, atot11405, atot11408]
  decide +kernel

theorem arows11416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11416 = true := by
  rw [show D2M8K2.u11416 = KTree.node D2M8K2.u11412 (nat_lit 24707476) (nat_lit 3473744117) (nat_lit 0) D2M8K2.u11415 from rfl, allE_node, arows11412, irow11416, arows11415]
  all_goals rfl

theorem atot11416 : totK PD2M8K2 D2M8K2.u11416 = [0, 0, 864824958668, 3053144820604, 2735635016364, 467096602560, 10194375460, 0] := by
  rw [show D2M8K2.u11416 = KTree.node D2M8K2.u11412 (nat_lit 24707476) (nat_lit 3473744117) (nat_lit 0) D2M8K2.u11415 from rfl, totK_node, atot11412, atot11415]
  decide +kernel

theorem arows11425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11425 = true := by
  rw [show D2M8K2.u11425 = KTree.node D2M8K2.u11421 (nat_lit 24714751) (nat_lit 2360761045) (nat_lit 0) D2M8K2.u11424 from rfl, allE_node, arows11421, irow11425, arows11424]
  all_goals rfl

theorem atot11425 : totK PD2M8K2 D2M8K2.u11425 = [0, 283783099808, 1306700048730, 2720889069062, 2372326639492, 430704946387, 10531122277, 0] := by
  rw [show D2M8K2.u11425 = KTree.node D2M8K2.u11421 (nat_lit 24714751) (nat_lit 2360761045) (nat_lit 0) D2M8K2.u11424 from rfl, totK_node, atot11421, atot11424]
  decide +kernel

theorem arows11432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11432 = true := by
  rw [show D2M8K2.u11432 = KTree.node D2M8K2.u11428 (nat_lit 24722866) (nat_lit 3888386033) (nat_lit 0) D2M8K2.u11431 from rfl, allE_node, arows11428, irow11432, arows11431]
  all_goals rfl

theorem atot11432 : totK PD2M8K2 D2M8K2.u11432 = [0, 821877154288, 2853570835268, 2791982165982, 748113785278, 38762704037, 0, 0] := by
  rw [show D2M8K2.u11432 = KTree.node D2M8K2.u11428 (nat_lit 24722866) (nat_lit 3888386033) (nat_lit 0) D2M8K2.u11431 from rfl, totK_node, atot11428, atot11431]
  decide +kernel

theorem arows11440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11440 = true := by
  rw [show D2M8K2.u11440 = KTree.node D2M8K2.u11436 (nat_lit 24732080) (nat_lit 3787791696) (nat_lit 0) D2M8K2.u11439 from rfl, allE_node, arows11436, irow11440, arows11439]
  all_goals rfl

theorem atot11440 : totK PD2M8K2 D2M8K2.u11440 = [0, 821030816755, 2953300220555, 2831993493514, 584266809243, 18030242193, 0, 0] := by
  rw [show D2M8K2.u11440 = KTree.node D2M8K2.u11436 (nat_lit 24732080) (nat_lit 3787791696) (nat_lit 0) D2M8K2.u11439 from rfl, totK_node, atot11436, atot11439]
  decide +kernel

theorem arows11447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11447 = true := by
  rw [show D2M8K2.u11447 = KTree.node D2M8K2.u11443 (nat_lit 24741896) (nat_lit 3899504972) (nat_lit 0) D2M8K2.u11446 from rfl, allE_node, arows11443, irow11447, arows11446]
  all_goals rfl

theorem atot11447 : totK PD2M8K2 D2M8K2.u11447 = [0, 62160131298, 1685713483831, 3726843506912, 1588266960606, 91529951513, 0, 0] := by
  rw [show D2M8K2.u11447 = KTree.node D2M8K2.u11443 (nat_lit 24741896) (nat_lit 3899504972) (nat_lit 0) D2M8K2.u11446 from rfl, totK_node, atot11443, atot11446]
  decide +kernel

theorem arows11457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11457 = true := by
  rw [show D2M8K2.u11457 = KTree.node D2M8K2.u11453 (nat_lit 24753117) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u11456 from rfl, allE_node, arows11453, irow11457, arows11456]
  all_goals rfl

theorem atot11457 : totK PD2M8K2 D2M8K2.u11457 = [0, 85430600343, 1091241509757, 3119855811402, 2435932808127, 353007702593, 6546549506, 0] := by
  rw [show D2M8K2.u11457 = KTree.node D2M8K2.u11453 (nat_lit 24753117) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u11456 from rfl, totK_node, atot11453, atot11456]
  decide +kernel

theorem arows11464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11464 = true := by
  rw [show D2M8K2.u11464 = KTree.node D2M8K2.u11460 (nat_lit 24763441) (nat_lit 828492598) (nat_lit 0) D2M8K2.u11463 from rfl, allE_node, arows11460, irow11464, arows11463]
  all_goals rfl

theorem atot11464 : totK PD2M8K2 D2M8K2.u11464 = [0, 840264591429, 2866578321113, 2757130269478, 742961273903, 38796216711, 0, 0] := by
  rw [show D2M8K2.u11464 = KTree.node D2M8K2.u11460 (nat_lit 24763441) (nat_lit 828492598) (nat_lit 0) D2M8K2.u11463 from rfl, totK_node, atot11460, atot11463]
  decide +kernel

theorem arows11472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11472 = true := by
  rw [show D2M8K2.u11472 = KTree.node D2M8K2.u11468 (nat_lit 24772971) (nat_lit 3695183521) (nat_lit 0) D2M8K2.u11471 from rfl, allE_node, arows11468, irow11472, arows11471]
  all_goals rfl

theorem atot11472 : totK PD2M8K2 D2M8K2.u11472 = [0, 833825680040, 2960928169173, 2812409535032, 588348469971, 18176614947, 0, 0] := by
  rw [show D2M8K2.u11472 = KTree.node D2M8K2.u11468 (nat_lit 24772971) (nat_lit 3695183521) (nat_lit 0) D2M8K2.u11471 from rfl, totK_node, atot11468, atot11471]
  decide +kernel

theorem arows11479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11479 = true := by
  rw [show D2M8K2.u11479 = KTree.node D2M8K2.u11475 (nat_lit 24780516) (nat_lit 3174420983) (nat_lit 0) D2M8K2.u11478 from rfl, allE_node, arows11475, irow11479, arows11478]
  all_goals rfl

theorem atot11479 : totK PD2M8K2 D2M8K2.u11479 = [0, 233675638286, 1983154630352, 3504980934207, 1393556063757, 84713903165, 0, 0] := by
  rw [show D2M8K2.u11479 = KTree.node D2M8K2.u11475 (nat_lit 24780516) (nat_lit 3174420983) (nat_lit 0) D2M8K2.u11478 from rfl, totK_node, atot11475, atot11478]
  decide +kernel

theorem arows11488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11488 = true := by
  rw [show D2M8K2.u11488 = KTree.node D2M8K2.u11484 (nat_lit 24794028) (nat_lit 3016233874) (nat_lit 0) D2M8K2.u11487 from rfl, allE_node, arows11484, irow11488, arows11487]
  all_goals rfl

theorem atot11488 : totK PD2M8K2 D2M8K2.u11488 = [0, 0, 964321491020, 3249024192559, 2536326271808, 356725264819, 6624648996, 0] := by
  rw [show D2M8K2.u11488 = KTree.node D2M8K2.u11484 (nat_lit 24794028) (nat_lit 3016233874) (nat_lit 0) D2M8K2.u11487 from rfl, totK_node, atot11484, atot11487]
  decide +kernel

theorem arows11495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11495 = true := by
  rw [show D2M8K2.u11495 = KTree.node D2M8K2.u11491 (nat_lit 24804297) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u11494 from rfl, allE_node, arows11491, irow11495, arows11494]
  all_goals rfl

theorem atot11495 : totK PD2M8K2 D2M8K2.u11495 = [0, 770655032679, 2795651457875, 2828594877232, 791162358252, 43768635552, 0, 0] := by
  rw [show D2M8K2.u11495 = KTree.node D2M8K2.u11491 (nat_lit 24804297) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u11494 from rfl, totK_node, atot11491, atot11494]
  decide +kernel

theorem arows11503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11503 = true := by
  rw [show D2M8K2.u11503 = KTree.node D2M8K2.u11499 (nat_lit 24810294) (nat_lit 3120211628) (nat_lit 0) D2M8K2.u11502 from rfl, allE_node, arows11499, irow11503, arows11502]
  all_goals rfl

theorem atot11503 : totK PD2M8K2 D2M8K2.u11503 = [0, 827867994437, 2867614061013, 2751234034113, 676333149762, 30421338049, 0, 0] := by
  rw [show D2M8K2.u11503 = KTree.node D2M8K2.u11499 (nat_lit 24810294) (nat_lit 3120211628) (nat_lit 0) D2M8K2.u11502 from rfl, totK_node, atot11499, atot11502]
  decide +kernel

theorem arows11510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11510 = true := by
  rw [show D2M8K2.u11510 = KTree.node D2M8K2.u11506 (nat_lit 24816999) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u11509 from rfl, allE_node, arows11506, irow11510, arows11509]
  all_goals rfl

theorem atot11510 : totK PD2M8K2 D2M8K2.u11510 = [0, 439668458485, 2320742074628, 3327739689672, 1059727299387, 48169809562, 0, 0] := by
  rw [show D2M8K2.u11510 = KTree.node D2M8K2.u11506 (nat_lit 24816999) (nat_lit 2890000784) (nat_lit 0) D2M8K2.u11509 from rfl, totK_node, atot11506, atot11509]
  decide +kernel

theorem arows11522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11522 = true := by
  rw [show D2M8K2.u11522 = KTree.node D2M8K2.u11518 (nat_lit 24832495) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u11521 from rfl, allE_node, arows11518, irow11522, arows11521]
  all_goals rfl

theorem atot11522 : totK PD2M8K2 D2M8K2.u11522 = [0, 0, 1338199313979, 3672211553525, 1994048022197, 139896041216, 0, 0] := by
  rw [show D2M8K2.u11522 = KTree.node D2M8K2.u11518 (nat_lit 24832495) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u11521 from rfl, totK_node, atot11518, atot11521]
  decide +kernel

theorem arows11529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11529 = true := by
  rw [show D2M8K2.u11529 = KTree.node D2M8K2.u11525 (nat_lit 24847782) (nat_lit 3822157977) (nat_lit 0) D2M8K2.u11528 from rfl, allE_node, arows11525, irow11529, arows11528]
  all_goals rfl

theorem atot11529 : totK PD2M8K2 D2M8K2.u11529 = [0, 833461993264, 2681426399502, 2629582329990, 995515244861, 123507885079, 1429815836, 0] := by
  rw [show D2M8K2.u11529 = KTree.node D2M8K2.u11525 (nat_lit 24847782) (nat_lit 3822157977) (nat_lit 0) D2M8K2.u11528 from rfl, totK_node, atot11525, atot11528]
  decide +kernel

theorem arows11537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11537 = true := by
  rw [show D2M8K2.u11537 = KTree.node D2M8K2.u11533 (nat_lit 24854216) (nat_lit 3821084053) (nat_lit 0) D2M8K2.u11536 from rfl, allE_node, arows11533, irow11537, arows11536]
  all_goals rfl

theorem atot11537 : totK PD2M8K2 D2M8K2.u11537 = [0, 832738749245, 2919091672334, 2830611890577, 642000749411, 18368003668, 0, 0] := by
  rw [show D2M8K2.u11537 = KTree.node D2M8K2.u11533 (nat_lit 24854216) (nat_lit 3821084053) (nat_lit 0) D2M8K2.u11536 from rfl, totK_node, atot11533, atot11536]
  decide +kernel

theorem arows11544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11544 = true := by
  rw [show D2M8K2.u11544 = KTree.node D2M8K2.u11540 (nat_lit 24867646) (nat_lit 3906004021) (nat_lit 0) D2M8K2.u11543 from rfl, allE_node, arows11540, irow11544, arows11543]
  all_goals rfl

theorem atot11544 : totK PD2M8K2 D2M8K2.u11544 = [0, 0, 1312693525817, 3541105487328, 2142070320845, 204268228284, 1323630408, 0] := by
  rw [show D2M8K2.u11544 = KTree.node D2M8K2.u11540 (nat_lit 24867646) (nat_lit 3906004021) (nat_lit 0) D2M8K2.u11543 from rfl, totK_node, atot11540, atot11543]
  decide +kernel

theorem arows11553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11553 = true := by
  rw [show D2M8K2.u11553 = KTree.node D2M8K2.u11549 (nat_lit 24880525) (nat_lit 1110680439) (nat_lit 0) D2M8K2.u11552 from rfl, allE_node, arows11549, irow11553, arows11552]
  all_goals rfl

theorem atot11553 : totK PD2M8K2 D2M8K2.u11553 = [261533257835, 580991266440, 889698434040, 2555710768903, 2429657880364, 429333776462, 10866219959, 0] := by
  rw [show D2M8K2.u11553 = KTree.node D2M8K2.u11549 (nat_lit 24880525) (nat_lit 1110680439) (nat_lit 0) D2M8K2.u11552 from rfl, totK_node, atot11549, atot11552]
  decide +kernel

theorem arows11560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11560 = true := by
  rw [show D2M8K2.u11560 = KTree.node D2M8K2.u11556 (nat_lit 24890954) (nat_lit 3905404412) (nat_lit 0) D2M8K2.u11559 from rfl, allE_node, arows11556, irow11560, arows11559]
  all_goals rfl

theorem atot11560 : totK PD2M8K2 D2M8K2.u11560 = [851448938434, 3025218052432, 2768579144630, 513626577150, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u11560 = KTree.node D2M8K2.u11556 (nat_lit 24890954) (nat_lit 3905404412) (nat_lit 0) D2M8K2.u11559 from rfl, totK_node, atot11556, atot11559]
  decide +kernel

theorem arows11568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11568 = true := by
  rw [show D2M8K2.u11568 = KTree.node D2M8K2.u11564 (nat_lit 24898219) (nat_lit 1731532500) (nat_lit 0) D2M8K2.u11567 from rfl, allE_node, arows11564, irow11568, arows11567]
  all_goals rfl

theorem atot11568 : totK PD2M8K2 D2M8K2.u11568 = [862794591548, 2970823344183, 2736456429886, 564327454728, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u11568 = KTree.node D2M8K2.u11564 (nat_lit 24898219) (nat_lit 1731532500) (nat_lit 0) D2M8K2.u11567 from rfl, totK_node, atot11564, atot11567]
  decide +kernel

theorem arows11575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11575 = true := by
  rw [show D2M8K2.u11575 = KTree.node D2M8K2.u11571 (nat_lit 24905429) (nat_lit 2375860474) (nat_lit 0) D2M8K2.u11574 from rfl, allE_node, arows11571, irow11575, arows11574]
  all_goals rfl

theorem atot11575 : totK PD2M8K2 D2M8K2.u11575 = [0, 1266845412819, 3520610928364, 2026707885045, 208085396561, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11575 = KTree.node D2M8K2.u11571 (nat_lit 24905429) (nat_lit 2375860474) (nat_lit 0) D2M8K2.u11574 from rfl, totK_node, atot11571, atot11574]
  decide +kernel

theorem arows11585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11585 = true := by
  rw [show D2M8K2.u11585 = KTree.node D2M8K2.u11581 (nat_lit 24921220) (nat_lit 3772546580) (nat_lit 0) D2M8K2.u11584 from rfl, allE_node, arows11581, irow11585, arows11584]
  all_goals rfl

theorem atot11585 : totK PD2M8K2 D2M8K2.u11585 = [355056847956, 2020745644470, 3333706286861, 1406906300050, 79362405039, 0, 0, 0] := by
  rw [show D2M8K2.u11585 = KTree.node D2M8K2.u11581 (nat_lit 24921220) (nat_lit 3772546580) (nat_lit 0) D2M8K2.u11584 from rfl, totK_node, atot11581, atot11584]
  decide +kernel

theorem arows11592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11592 = true := by
  rw [show D2M8K2.u11592 = KTree.node D2M8K2.u11588 (nat_lit 24932262) (nat_lit 2895158641) (nat_lit 0) D2M8K2.u11591 from rfl, allE_node, arows11588, irow11592, arows11591]
  all_goals rfl

theorem atot11592 : totK PD2M8K2 D2M8K2.u11592 = [690473378918, 2610022845013, 2983621471229, 930228897821, 50646263903, 0, 0, 0] := by
  rw [show D2M8K2.u11592 = KTree.node D2M8K2.u11588 (nat_lit 24932262) (nat_lit 2895158641) (nat_lit 0) D2M8K2.u11591 from rfl, totK_node, atot11588, atot11591]
  decide +kernel

theorem arows11600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11600 = true := by
  rw [show D2M8K2.u11600 = KTree.node D2M8K2.u11596 (nat_lit 24939531) (nat_lit 3724991613) (nat_lit 0) D2M8K2.u11599 from rfl, allE_node, arows11596, irow11600, arows11599]
  all_goals rfl

theorem atot11600 : totK PD2M8K2 D2M8K2.u11600 = [917836469674, 3080366164126, 2734602278150, 538436715660, 16977354800, 0, 0, 0] := by
  rw [show D2M8K2.u11600 = KTree.node D2M8K2.u11596 (nat_lit 24939531) (nat_lit 3724991613) (nat_lit 0) D2M8K2.u11599 from rfl, totK_node, atot11596, atot11599]
  decide +kernel

theorem arows11607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11607 = true := by
  rw [show D2M8K2.u11607 = KTree.node D2M8K2.u11603 (nat_lit 24950168) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u11606 from rfl, allE_node, arows11603, irow11607, arows11606]
  all_goals rfl

theorem atot11607 : totK PD2M8K2 D2M8K2.u11607 = [36951561255, 1175259430691, 3038276904135, 2330326571567, 620793843543, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11607 = KTree.node D2M8K2.u11603 (nat_lit 24950168) (nat_lit 3613870797) (nat_lit 0) D2M8K2.u11606 from rfl, totK_node, atot11603, atot11606]
  decide +kernel

theorem arows11616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11616 = true := by
  rw [show D2M8K2.u11616 = KTree.node D2M8K2.u11612 (nat_lit 24956958) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u11615 from rfl, allE_node, arows11612, irow11616, arows11615]
  all_goals rfl

theorem atot11616 : totK PD2M8K2 D2M8K2.u11616 = [0, 912228165024, 3073871252398, 2739228676479, 504981132280, 10378741320, 0, 0] := by
  rw [show D2M8K2.u11616 = KTree.node D2M8K2.u11612 (nat_lit 24956958) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u11615 from rfl, totK_node, atot11612, atot11615]
  decide +kernel

theorem arows11623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11623 = true := by
  rw [show D2M8K2.u11623 = KTree.node D2M8K2.u11619 (nat_lit 24964434) (nat_lit 2594507190) (nat_lit 0) D2M8K2.u11622 from rfl, allE_node, arows11619, irow11623, arows11622]
  all_goals rfl

theorem atot11623 : totK PD2M8K2 D2M8K2.u11623 = [413201475250, 1552205802244, 2573334994067, 2197862796865, 454455114904, 10717512769, 0, 0] := by
  rw [show D2M8K2.u11623 = KTree.node D2M8K2.u11619 (nat_lit 24964434) (nat_lit 2594507190) (nat_lit 0) D2M8K2.u11622 from rfl, totK_node, atot11619, atot11622]
  decide +kernel

theorem arows11631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11631 = true := by
  rw [show D2M8K2.u11631 = KTree.node D2M8K2.u11627 (nat_lit 24971807) (nat_lit 2028239749) (nat_lit 0) D2M8K2.u11630 from rfl, allE_node, arows11627, irow11631, arows11630]
  all_goals rfl

theorem atot11631 : totK PD2M8K2 D2M8K2.u11631 = [817677575662, 2839698239452, 2807791570395, 765846957187, 38763934174, 0, 0, 0] := by
  rw [show D2M8K2.u11631 = KTree.node D2M8K2.u11627 (nat_lit 24971807) (nat_lit 2028239749) (nat_lit 0) D2M8K2.u11630 from rfl, totK_node, atot11627, atot11630]
  decide +kernel

theorem arows11638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11638 = true := by
  rw [show D2M8K2.u11638 = KTree.node D2M8K2.u11634 (nat_lit 24981008) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u11637 from rfl, allE_node, arows11634, irow11638, arows11637]
  all_goals rfl

theorem atot11638 : totK PD2M8K2 D2M8K2.u11638 = [817825086167, 2946943449516, 2851244388738, 583747954518, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u11638 = KTree.node D2M8K2.u11634 (nat_lit 24981008) (nat_lit 3691383965) (nat_lit 0) D2M8K2.u11637 from rfl, totK_node, atot11634, atot11637]
  decide +kernel

theorem arows11649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11649 = true := by
  rw [show D2M8K2.u11649 = KTree.node D2M8K2.u11645 (nat_lit 24988207) (nat_lit 1228600436) (nat_lit 0) D2M8K2.u11648 from rfl, allE_node, arows11645, irow11649, arows11648]
  all_goals rfl

theorem atot11649 : totK PD2M8K2 D2M8K2.u11649 = [54703274150, 1426271284703, 3502390204208, 1925462523144, 175563004305, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11649 = KTree.node D2M8K2.u11645 (nat_lit 24988207) (nat_lit 1228600436) (nat_lit 0) D2M8K2.u11648 from rfl, totK_node, atot11645, atot11648]
  decide +kernel

theorem arows11656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11656 = true := by
  rw [show D2M8K2.u11656 = KTree.node D2M8K2.u11652 (nat_lit 24996782) (nat_lit 3458350381) (nat_lit 0) D2M8K2.u11655 from rfl, allE_node, arows11652, irow11656, arows11655]
  all_goals rfl

theorem atot11656 : totK PD2M8K2 D2M8K2.u11656 = [0, 861507420195, 3108188499754, 2632788269432, 459711558144, 15028818242, 0, 0] := by
  rw [show D2M8K2.u11656 = KTree.node D2M8K2.u11652 (nat_lit 24996782) (nat_lit 3458350381) (nat_lit 0) D2M8K2.u11655 from rfl, totK_node, atot11652, atot11655]
  decide +kernel

theorem arows11664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11664 = true := by
  rw [show D2M8K2.u11664 = KTree.node D2M8K2.u11660 (nat_lit 25050357) (nat_lit 1741627740) (nat_lit 0) D2M8K2.u11663 from rfl, allE_node, arows11660, irow11664, arows11663]
  all_goals rfl

theorem atot11664 : totK PD2M8K2 D2M8K2.u11664 = [775656429052, 2765415540497, 2759612139585, 810987591878, 76689923940, 2561774784, 0, 0] := by
  rw [show D2M8K2.u11664 = KTree.node D2M8K2.u11660 (nat_lit 25050357) (nat_lit 1741627740) (nat_lit 0) D2M8K2.u11663 from rfl, totK_node, atot11660, atot11663]
  decide +kernel

theorem arows11671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11671 = true := by
  rw [show D2M8K2.u11671 = KTree.node D2M8K2.u11667 (nat_lit 25056784) (nat_lit 3688860793) (nat_lit 0) D2M8K2.u11670 from rfl, allE_node, arows11667, irow11671, arows11670]
  all_goals rfl

theorem atot11671 : totK PD2M8K2 D2M8K2.u11671 = [730370407816, 2643984896091, 2902487862910, 915364095319, 50466680850, 0, 0, 0] := by
  rw [show D2M8K2.u11671 = KTree.node D2M8K2.u11667 (nat_lit 25056784) (nat_lit 3688860793) (nat_lit 0) D2M8K2.u11670 from rfl, totK_node, atot11667, atot11670]
  decide +kernel

theorem arows11680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11680 = true := by
  rw [show D2M8K2.u11680 = KTree.node D2M8K2.u11676 (nat_lit 25063933) (nat_lit 1183964331) (nat_lit 0) D2M8K2.u11679 from rfl, allE_node, arows11676, irow11680, arows11679]
  all_goals rfl

theorem atot11680 : totK PD2M8K2 D2M8K2.u11680 = [527805388803, 2548634357593, 3193502525178, 882060949633, 37574046328, 0, 0, 0] := by
  rw [show D2M8K2.u11680 = KTree.node D2M8K2.u11676 (nat_lit 25063933) (nat_lit 1183964331) (nat_lit 0) D2M8K2.u11679 from rfl, totK_node, atot11676, atot11679]
  decide +kernel

theorem arows11687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11687 = true := by
  rw [show D2M8K2.u11687 = KTree.node D2M8K2.u11683 (nat_lit 25076756) (nat_lit 3239739834) (nat_lit 0) D2M8K2.u11686 from rfl, allE_node, arows11683, irow11687, arows11686]
  all_goals rfl

theorem atot11687 : totK PD2M8K2 D2M8K2.u11687 = [0, 1248561468744, 3607727409136, 2130326285143, 185782528711, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11687 = KTree.node D2M8K2.u11683 (nat_lit 25076756) (nat_lit 3239739834) (nat_lit 0) D2M8K2.u11686 from rfl, totK_node, atot11683, atot11686]
  decide +kernel

theorem arows11695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11695 = true := by
  rw [show D2M8K2.u11695 = KTree.node D2M8K2.u11691 (nat_lit 25090567) (nat_lit 2374171017) (nat_lit 0) D2M8K2.u11694 from rfl, allE_node, arows11691, irow11695, arows11694]
  all_goals rfl

theorem atot11695 : totK PD2M8K2 D2M8K2.u11695 = [488941958552, 2043381080218, 2867540084102, 1495968400095, 228947769458, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11695 = KTree.node D2M8K2.u11691 (nat_lit 25090567) (nat_lit 2374171017) (nat_lit 0) D2M8K2.u11694 from rfl, totK_node, atot11691, atot11694]
  decide +kernel

theorem arows11702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11702 = true := by
  rw [show D2M8K2.u11702 = KTree.node D2M8K2.u11698 (nat_lit 25097450) (nat_lit 4062864674) (nat_lit 0) D2M8K2.u11701 from rfl, allE_node, arows11698, irow11702, arows11701]
  all_goals rfl

theorem atot11702 : totK PD2M8K2 D2M8K2.u11702 = [741065965101, 2697157571566, 2874589288831, 888828639913, 50598507583, 0, 0, 0] := by
  rw [show D2M8K2.u11702 = KTree.node D2M8K2.u11698 (nat_lit 25097450) (nat_lit 4062864674) (nat_lit 0) D2M8K2.u11701 from rfl, totK_node, atot11698, atot11701]
  decide +kernel

theorem arows11712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11712 = true := by
  rw [show D2M8K2.u11712 = KTree.node D2M8K2.u11708 (nat_lit 25110584) (nat_lit 2268080519) (nat_lit 0) D2M8K2.u11711 from rfl, allE_node, arows11708, irow11712, arows11711]
  all_goals rfl

theorem atot11712 : totK PD2M8K2 D2M8K2.u11712 = [427983732745, 1991429610408, 3064733186836, 1535204039896, 143283877812, 1310285577, 0, 0] := by
  rw [show D2M8K2.u11712 = KTree.node D2M8K2.u11708 (nat_lit 25110584) (nat_lit 2268080519) (nat_lit 0) D2M8K2.u11711 from rfl, totK_node, atot11708, atot11711]
  decide +kernel

theorem arows11719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11719 = true := by
  rw [show D2M8K2.u11719 = KTree.node D2M8K2.u11715 (nat_lit 25119425) (nat_lit 2221654230) (nat_lit 0) D2M8K2.u11718 from rfl, allE_node, arows11715, irow11719, arows11718]
  all_goals rfl

theorem atot11719 : totK PD2M8K2 D2M8K2.u11719 = [0, 1163885984546, 3403118005696, 2352948883137, 298974074040, 4879840392, 0, 0] := by
  rw [show D2M8K2.u11719 = KTree.node D2M8K2.u11715 (nat_lit 25119425) (nat_lit 2221654230) (nat_lit 0) D2M8K2.u11718 from rfl, totK_node, atot11715, atot11718]
  decide +kernel

theorem arows11727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11727 = true := by
  rw [show D2M8K2.u11727 = KTree.node D2M8K2.u11723 (nat_lit 25133190) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u11726 from rfl, allE_node, arows11723, irow11727, arows11726]
  all_goals rfl

theorem atot11727 : totK PD2M8K2 D2M8K2.u11727 = [0, 851597423783, 2954970343320, 2737705710997, 582730988239, 23120318498, 0, 0] := by
  rw [show D2M8K2.u11727 = KTree.node D2M8K2.u11723 (nat_lit 25133190) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u11726 from rfl, totK_node, atot11723, atot11726]
  decide +kernel

theorem arows11734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11734 = true := by
  rw [show D2M8K2.u11734 = KTree.node D2M8K2.u11730 (nat_lit 25143912) (nat_lit 3534038886) (nat_lit 0) D2M8K2.u11733 from rfl, allE_node, arows11730, irow11734, arows11733]
  all_goals rfl

theorem atot11734 : totK PD2M8K2 D2M8K2.u11734 = [0, 830799258407, 3013606515449, 2745838235416, 498754903082, 15344305730, 0, 0] := by
  rw [show D2M8K2.u11734 = KTree.node D2M8K2.u11730 (nat_lit 25143912) (nat_lit 3534038886) (nat_lit 0) D2M8K2.u11733 from rfl, totK_node, atot11730, atot11733]
  decide +kernel

theorem arows11743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11743 = true := by
  rw [show D2M8K2.u11743 = KTree.node D2M8K2.u11739 (nat_lit 25151649) (nat_lit 1284860970) (nat_lit 0) D2M8K2.u11742 from rfl, allE_node, arows11739, irow11743, arows11742]
  all_goals rfl

theorem atot11743 : totK PD2M8K2 D2M8K2.u11743 = [0, 382286559831, 2102132282321, 3217057228365, 1236486357051, 113711090292, 1275377855, 0] := by
  rw [show D2M8K2.u11743 = KTree.node D2M8K2.u11739 (nat_lit 25151649) (nat_lit 1284860970) (nat_lit 0) D2M8K2.u11742 from rfl, totK_node, atot11739, atot11742]
  decide +kernel

theorem arows11750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11750 = true := by
  rw [show D2M8K2.u11750 = KTree.node D2M8K2.u11746 (nat_lit 25164659) (nat_lit 2829963776) (nat_lit 0) D2M8K2.u11749 from rfl, allE_node, arows11746, irow11750, arows11749]
  all_goals rfl

theorem atot11750 : totK PD2M8K2 D2M8K2.u11750 = [0, 38616506213, 1568501848561, 3777138268960, 1562540249223, 78893295842, 0, 0] := by
  rw [show D2M8K2.u11750 = KTree.node D2M8K2.u11746 (nat_lit 25164659) (nat_lit 2829963776) (nat_lit 0) D2M8K2.u11749 from rfl, totK_node, atot11746, atot11749]
  decide +kernel

theorem arows11758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11758 = true := by
  rw [show D2M8K2.u11758 = KTree.node D2M8K2.u11754 (nat_lit 25179922) (nat_lit 3048806250) (nat_lit 0) D2M8K2.u11757 from rfl, allE_node, arows11754, irow11758, arows11757]
  all_goals rfl

theorem atot11758 : totK PD2M8K2 D2M8K2.u11758 = [0, 827657543090, 2867451338463, 2774073930622, 771184023392, 43498335072, 0, 0] := by
  rw [show D2M8K2.u11758 = KTree.node D2M8K2.u11754 (nat_lit 25179922) (nat_lit 3048806250) (nat_lit 0) D2M8K2.u11757 from rfl, totK_node, atot11754, atot11757]
  decide +kernel

theorem arows11765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11765 = true := by
  rw [show D2M8K2.u11765 = KTree.node D2M8K2.u11761 (nat_lit 25187381) (nat_lit 2363828081) (nat_lit 0) D2M8K2.u11764 from rfl, allE_node, arows11761, irow11765, arows11764]
  all_goals rfl

theorem atot11765 : totK PD2M8K2 D2M8K2.u11765 = [0, 834984562602, 3007719280808, 2855153297613, 562476981588, 15194025302, 0, 0] := by
  rw [show D2M8K2.u11765 = KTree.node D2M8K2.u11761 (nat_lit 25187381) (nat_lit 2363828081) (nat_lit 0) D2M8K2.u11764 from rfl, totK_node, atot11761, atot11764]
  decide +kernel

theorem arows11778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11778 = true := by
  rw [show D2M8K2.u11778 = KTree.node D2M8K2.u11774 (nat_lit 25215193) (nat_lit 1504782725) (nat_lit 0) D2M8K2.u11777 from rfl, allE_node, arows11774, irow11778, arows11777]
  all_goals rfl

theorem atot11778 : totK PD2M8K2 D2M8K2.u11778 = [0, 854005564427, 2963219943569, 2776674005399, 573298273534, 19125631575, 0, 0] := by
  rw [show D2M8K2.u11778 = KTree.node D2M8K2.u11774 (nat_lit 25215193) (nat_lit 1504782725) (nat_lit 0) D2M8K2.u11777 from rfl, totK_node, atot11774, atot11777]
  decide +kernel

theorem arows11785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11785 = true := by
  rw [show D2M8K2.u11785 = KTree.node D2M8K2.u11781 (nat_lit 25222032) (nat_lit 3736141441) (nat_lit 0) D2M8K2.u11784 from rfl, allE_node, arows11781, irow11785, arows11784]
  all_goals rfl

theorem atot11785 : totK PD2M8K2 D2M8K2.u11785 = [0, 721875904067, 2760126906570, 2926432631702, 791756451197, 37138651511, 0, 0] := by
  rw [show D2M8K2.u11785 = KTree.node D2M8K2.u11781 (nat_lit 25222032) (nat_lit 3736141441) (nat_lit 0) D2M8K2.u11784 from rfl, totK_node, atot11781, atot11784]
  decide +kernel

theorem arows11793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11793 = true := by
  rw [show D2M8K2.u11793 = KTree.node D2M8K2.u11789 (nat_lit 25232329) (nat_lit 1503962714) (nat_lit 0) D2M8K2.u11792 from rfl, allE_node, arows11789, irow11793, arows11792]
  all_goals rfl

theorem atot11793 : totK PD2M8K2 D2M8K2.u11793 = [0, 821872840808, 2939011471556, 2804705713632, 576375607344, 18575896284, 0, 0] := by
  rw [show D2M8K2.u11793 = KTree.node D2M8K2.u11789 (nat_lit 25232329) (nat_lit 1503962714) (nat_lit 0) D2M8K2.u11792 from rfl, totK_node, atot11789, atot11792]
  decide +kernel

theorem arows11800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11800 = true := by
  rw [show D2M8K2.u11800 = KTree.node D2M8K2.u11796 (nat_lit 25239776) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u11799 from rfl, allE_node, arows11796, irow11800, arows11799]
  all_goals rfl

theorem atot11800 : totK PD2M8K2 D2M8K2.u11800 = [0, 0, 1246309505371, 3551947019899, 2051571990370, 193416021524, 1206465782, 0] := by
  rw [show D2M8K2.u11800 = KTree.node D2M8K2.u11796 (nat_lit 25239776) (nat_lit 3747989932) (nat_lit 0) D2M8K2.u11799 from rfl, totK_node, atot11796, atot11799]
  decide +kernel

theorem arows11809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11809 = true := by
  rw [show D2M8K2.u11809 = KTree.node D2M8K2.u11805 (nat_lit 25251364) (nat_lit 3699021391) (nat_lit 0) D2M8K2.u11808 from rfl, allE_node, arows11805, irow11809, arows11808]
  all_goals rfl

theorem atot11809 : totK PD2M8K2 D2M8K2.u11809 = [0, 175422674038, 1168692398377, 2850606547568, 2274810383489, 461732931200, 17590593026, 0] := by
  rw [show D2M8K2.u11809 = KTree.node D2M8K2.u11805 (nat_lit 25251364) (nat_lit 3699021391) (nat_lit 0) D2M8K2.u11808 from rfl, totK_node, atot11805, atot11808]
  decide +kernel

theorem arows11816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11816 = true := by
  rw [show D2M8K2.u11816 = KTree.node D2M8K2.u11812 (nat_lit 25302283) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u11815 from rfl, allE_node, arows11812, irow11816, arows11815]
  all_goals rfl

theorem atot11816 : totK PD2M8K2 D2M8K2.u11816 = [0, 820485542437, 3005307155655, 2819019623098, 566614303259, 16324156210, 0, 0] := by
  rw [show D2M8K2.u11816 = KTree.node D2M8K2.u11812 (nat_lit 25302283) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u11815 from rfl, totK_node, atot11812, atot11815]
  decide +kernel

theorem arows11824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11824 = true := by
  rw [show D2M8K2.u11824 = KTree.node D2M8K2.u11820 (nat_lit 25308810) (nat_lit 3803558289) (nat_lit 0) D2M8K2.u11823 from rfl, allE_node, arows11820, irow11824, arows11823]
  all_goals rfl

theorem atot11824 : totK PD2M8K2 D2M8K2.u11824 = [0, 922297563758, 3037228389531, 2707152828547, 528032980833, 17735875666, 0, 0] := by
  rw [show D2M8K2.u11824 = KTree.node D2M8K2.u11820 (nat_lit 25308810) (nat_lit 3803558289) (nat_lit 0) D2M8K2.u11823 from rfl, totK_node, atot11820, atot11823]
  decide +kernel

theorem arows11831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11831 = true := by
  rw [show D2M8K2.u11831 = KTree.node D2M8K2.u11827 (nat_lit 25319984) (nat_lit 3798690481) (nat_lit 0) D2M8K2.u11830 from rfl, allE_node, arows11827, irow11831, arows11830]
  all_goals rfl

theorem atot11831 : totK PD2M8K2 D2M8K2.u11831 = [0, 111279211669, 1753568311620, 3565000341386, 1507871645375, 107206890470, 1103454931, 0] := by
  rw [show D2M8K2.u11831 = KTree.node D2M8K2.u11827 (nat_lit 25319984) (nat_lit 3798690481) (nat_lit 0) D2M8K2.u11830 from rfl, totK_node, atot11827, atot11830]
  decide +kernel

theorem arows11841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11841 = true := by
  rw [show D2M8K2.u11841 = KTree.node D2M8K2.u11837 (nat_lit 25333157) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u11840 from rfl, allE_node, arows11837, irow11841, arows11840]
  all_goals rfl

theorem atot11841 : totK PD2M8K2 D2M8K2.u11841 = [0, 270182989682, 1675439341469, 3146120975457, 1686766487424, 204292245010, 4779662215, 0] := by
  rw [show D2M8K2.u11841 = KTree.node D2M8K2.u11837 (nat_lit 25333157) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u11840 from rfl, totK_node, atot11837, atot11840]
  decide +kernel

theorem arows11848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11848 = true := by
  rw [show D2M8K2.u11848 = KTree.node D2M8K2.u11844 (nat_lit 25344331) (nat_lit 1785918393) (nat_lit 0) D2M8K2.u11847 from rfl, allE_node, arows11844, irow11848, arows11847]
  all_goals rfl

theorem atot11848 : totK PD2M8K2 D2M8K2.u11848 = [0, 796613395686, 2849417392091, 2838870366167, 728285303831, 34131549329, 0, 0] := by
  rw [show D2M8K2.u11848 = KTree.node D2M8K2.u11844 (nat_lit 25344331) (nat_lit 1785918393) (nat_lit 0) D2M8K2.u11847 from rfl, totK_node, atot11844, atot11847]
  decide +kernel

theorem arows11856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11856 = true := by
  rw [show D2M8K2.u11856 = KTree.node D2M8K2.u11852 (nat_lit 25357493) (nat_lit 2300761511) (nat_lit 0) D2M8K2.u11855 from rfl, allE_node, arows11852, irow11856, arows11855]
  all_goals rfl

theorem atot11856 : totK PD2M8K2 D2M8K2.u11856 = [191552386262, 1055075380577, 2577326163741, 2661568410861, 690864848892, 31566124419, 0, 0] := by
  rw [show D2M8K2.u11856 = KTree.node D2M8K2.u11852 (nat_lit 25357493) (nat_lit 2300761511) (nat_lit 0) D2M8K2.u11855 from rfl, totK_node, atot11852, atot11855]
  decide +kernel

theorem arows11863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11863 = true := by
  rw [show D2M8K2.u11863 = KTree.node D2M8K2.u11859 (nat_lit 25389032) (nat_lit 3943017048) (nat_lit 0) D2M8K2.u11862 from rfl, allE_node, arows11859, irow11863, arows11862]
  all_goals rfl

theorem atot11863 : totK PD2M8K2 D2M8K2.u11863 = [912253374292, 3080008069550, 2680626554719, 486302850915, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u11863 = KTree.node D2M8K2.u11859 (nat_lit 25389032) (nat_lit 3943017048) (nat_lit 0) D2M8K2.u11862 from rfl, totK_node, atot11859, atot11862]
  decide +kernel

theorem arows11872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11872 = true := by
  rw [show D2M8K2.u11872 = KTree.node D2M8K2.u11868 (nat_lit 25395770) (nat_lit 3935990336) (nat_lit 0) D2M8K2.u11871 from rfl, allE_node, arows11868, irow11872, arows11871]
  all_goals rfl

theorem atot11872 : totK PD2M8K2 D2M8K2.u11872 = [849041245619, 2928973330966, 2780077907977, 590198725498, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u11872 = KTree.node D2M8K2.u11868 (nat_lit 25395770) (nat_lit 3935990336) (nat_lit 0) D2M8K2.u11871 from rfl, totK_node, atot11868, atot11871]
  decide +kernel

theorem arows11879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11879 = true := by
  rw [show D2M8K2.u11879 = KTree.node D2M8K2.u11875 (nat_lit 25402946) (nat_lit 3270512673) (nat_lit 0) D2M8K2.u11878 from rfl, allE_node, arows11875, irow11879, arows11878]
  all_goals rfl

theorem atot11879 : totK PD2M8K2 D2M8K2.u11879 = [19692840307, 1361159832166, 3483309793414, 1952888709363, 208955364530, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11879 = KTree.node D2M8K2.u11875 (nat_lit 25402946) (nat_lit 3270512673) (nat_lit 0) D2M8K2.u11878 from rfl, totK_node, atot11875, atot11878]
  decide +kernel

theorem arows11887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11887 = true := by
  rw [show D2M8K2.u11887 = KTree.node D2M8K2.u11883 (nat_lit 25416684) (nat_lit 3185297290) (nat_lit 0) D2M8K2.u11886 from rfl, allE_node, arows11883, irow11887, arows11886]
  all_goals rfl

theorem atot11887 : totK PD2M8K2 D2M8K2.u11887 = [336184739765, 1909845693517, 3387848410175, 1486171179250, 78520602526, 0, 0, 0] := by
  rw [show D2M8K2.u11887 = KTree.node D2M8K2.u11883 (nat_lit 25416684) (nat_lit 3185297290) (nat_lit 0) D2M8K2.u11886 from rfl, totK_node, atot11883, atot11886]
  decide +kernel

theorem arows11894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11894 = true := by
  rw [show D2M8K2.u11894 = KTree.node D2M8K2.u11890 (nat_lit 25429998) (nat_lit 3185332478) (nat_lit 0) D2M8K2.u11893 from rfl, allE_node, arows11890, irow11894, arows11893]
  all_goals rfl

theorem atot11894 : totK PD2M8K2 D2M8K2.u11894 = [761739540740, 2736762923348, 2882639107118, 874341139198, 49442923769, 0, 0, 0] := by
  rw [show D2M8K2.u11894 = KTree.node D2M8K2.u11890 (nat_lit 25429998) (nat_lit 3185332478) (nat_lit 0) D2M8K2.u11893 from rfl, totK_node, atot11890, atot11893]
  decide +kernel

theorem arows11905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11905 = true := by
  rw [show D2M8K2.u11905 = KTree.node D2M8K2.u11901 (nat_lit 25437068) (nat_lit 3724550032) (nat_lit 0) D2M8K2.u11904 from rfl, allE_node, arows11901, irow11905, arows11904]
  all_goals rfl

theorem atot11905 : totK PD2M8K2 D2M8K2.u11905 = [812090461301, 2969728006420, 2856573815890, 594000255213, 18214542822, 0, 0, 0] := by
  rw [show D2M8K2.u11905 = KTree.node D2M8K2.u11901 (nat_lit 25437068) (nat_lit 3724550032) (nat_lit 0) D2M8K2.u11904 from rfl, totK_node, atot11901, atot11904]
  decide +kernel

theorem arows11912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11912 = true := by
  rw [show D2M8K2.u11912 = KTree.node D2M8K2.u11908 (nat_lit 25447712) (nat_lit 3830058444) (nat_lit 0) D2M8K2.u11911 from rfl, allE_node, arows11908, irow11912, arows11911]
  all_goals rfl

theorem atot11912 : totK PD2M8K2 D2M8K2.u11912 = [90526578066, 1256473654575, 2970979531348, 2280741108033, 619592819111, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11912 = KTree.node D2M8K2.u11908 (nat_lit 25447712) (nat_lit 3830058444) (nat_lit 0) D2M8K2.u11911 from rfl, totK_node, atot11908, atot11911]
  decide +kernel

theorem arows11920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11920 = true := by
  rw [show D2M8K2.u11920 = KTree.node D2M8K2.u11916 (nat_lit 25454677) (nat_lit 1217006779) (nat_lit 0) D2M8K2.u11919 from rfl, allE_node, arows11916, irow11920, arows11919]
  all_goals rfl

theorem atot11920 : totK PD2M8K2 D2M8K2.u11920 = [0, 905653961711, 3100395743274, 2712979572964, 497742781332, 10378741320, 0, 0] := by
  rw [show D2M8K2.u11920 = KTree.node D2M8K2.u11916 (nat_lit 25454677) (nat_lit 1217006779) (nat_lit 0) D2M8K2.u11919 from rfl, totK_node, atot11916, atot11919]
  decide +kernel

theorem arows11927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11927 = true := by
  rw [show D2M8K2.u11927 = KTree.node D2M8K2.u11923 (nat_lit 25461984) (nat_lit 2800330364) (nat_lit 0) D2M8K2.u11926 from rfl, allE_node, arows11923, irow11927, arows11926]
  all_goals rfl

theorem atot11927 : totK PD2M8K2 D2M8K2.u11927 = [413264604107, 1512722038474, 2557732527158, 2244391787244, 461886209414, 10717512769, 0, 0] := by
  rw [show D2M8K2.u11927 = KTree.node D2M8K2.u11923 (nat_lit 25461984) (nat_lit 2800330364) (nat_lit 0) D2M8K2.u11926 from rfl, totK_node, atot11923, atot11926]
  decide +kernel

theorem arows11936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11936 = true := by
  rw [show D2M8K2.u11936 = KTree.node D2M8K2.u11932 (nat_lit 25510833) (nat_lit 1790998092) (nat_lit 0) D2M8K2.u11935 from rfl, allE_node, arows11932, irow11936, arows11935]
  all_goals rfl

theorem atot11936 : totK PD2M8K2 D2M8K2.u11936 = [781453099037, 2812359599881, 2864531008328, 776011740637, 38761049754, 0, 0, 0] := by
  rw [show D2M8K2.u11936 = KTree.node D2M8K2.u11932 (nat_lit 25510833) (nat_lit 1790998092) (nat_lit 0) D2M8K2.u11935 from rfl, totK_node, atot11932, atot11935]
  decide +kernel

theorem arows11943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11943 = true := by
  rw [show D2M8K2.u11943 = KTree.node D2M8K2.u11939 (nat_lit 25520054) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u11942 from rfl, allE_node, arows11939, irow11943, arows11942]
  all_goals rfl

theorem atot11943 : totK PD2M8K2 D2M8K2.u11943 = [821066702185, 2948271578612, 2844532929963, 590772076819, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u11943 = KTree.node D2M8K2.u11939 (nat_lit 25520054) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u11942 from rfl, totK_node, atot11939, atot11942]
  decide +kernel

theorem arows11951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11951 = true := by
  rw [show D2M8K2.u11951 = KTree.node D2M8K2.u11947 (nat_lit 25527221) (nat_lit 2220764233) (nat_lit 0) D2M8K2.u11950 from rfl, allE_node, arows11947, irow11951, arows11950]
  all_goals rfl

theorem atot11951 : totK PD2M8K2 D2M8K2.u11951 = [91570829045, 1450276055348, 3440463270102, 1945167619469, 179897087005, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11951 = KTree.node D2M8K2.u11947 (nat_lit 25527221) (nat_lit 2220764233) (nat_lit 0) D2M8K2.u11950 from rfl, totK_node, atot11947, atot11950]
  decide +kernel

theorem arows11958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11958 = true := by
  rw [show D2M8K2.u11958 = KTree.node D2M8K2.u11954 (nat_lit 25539229) (nat_lit 978605697) (nat_lit 0) D2M8K2.u11957 from rfl, allE_node, arows11954, irow11958, arows11957]
  all_goals rfl

theorem atot11958 : totK PD2M8K2 D2M8K2.u11958 = [0, 934570103644, 3163854841464, 2572352591827, 436575755901, 14158861562, 0, 0] := by
  rw [show D2M8K2.u11958 = KTree.node D2M8K2.u11954 (nat_lit 25539229) (nat_lit 978605697) (nat_lit 0) D2M8K2.u11957 from rfl, totK_node, atot11954, atot11957]
  decide +kernel

theorem arows11968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11968 = true := by
  rw [show D2M8K2.u11968 = KTree.node D2M8K2.u11964 (nat_lit 25547859) (nat_lit 2466642975) (nat_lit 0) D2M8K2.u11967 from rfl, allE_node, arows11964, irow11968, arows11967]
  all_goals rfl

theorem atot11968 : totK PD2M8K2 D2M8K2.u11968 = [726588799580, 2598248404903, 2747852461027, 971618985756, 120238649393, 3667207281, 0, 0] := by
  rw [show D2M8K2.u11968 = KTree.node D2M8K2.u11964 (nat_lit 25547859) (nat_lit 2466642975) (nat_lit 0) D2M8K2.u11967 from rfl, totK_node, atot11964, atot11967]
  decide +kernel

theorem arows11975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11975 = true := by
  rw [show D2M8K2.u11975 = KTree.node D2M8K2.u11971 (nat_lit 25554285) (nat_lit 1478205480) (nat_lit 0) D2M8K2.u11974 from rfl, allE_node, arows11971, irow11975, arows11974]
  all_goals rfl

theorem atot11975 : totK PD2M8K2 D2M8K2.u11975 = [747048398939, 2697416420488, 2856970373718, 894121935836, 50466742326, 0, 0, 0] := by
  rw [show D2M8K2.u11975 = KTree.node D2M8K2.u11971 (nat_lit 25554285) (nat_lit 1478205480) (nat_lit 0) D2M8K2.u11974 from rfl, totK_node, atot11971, atot11974]
  decide +kernel

theorem arows11983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11983 = true := by
  rw [show D2M8K2.u11983 = KTree.node D2M8K2.u11979 (nat_lit 25561406) (nat_lit 2481466265) (nat_lit 0) D2M8K2.u11982 from rfl, allE_node, arows11979, irow11983, arows11982]
  all_goals rfl

theorem atot11983 : totK PD2M8K2 D2M8K2.u11983 = [552723083876, 2584112406567, 3161787991102, 856709219096, 36492763016, 0, 0, 0] := by
  rw [show D2M8K2.u11983 = KTree.node D2M8K2.u11979 (nat_lit 25561406) (nat_lit 2481466265) (nat_lit 0) D2M8K2.u11982 from rfl, totK_node, atot11979, atot11982]
  decide +kernel

theorem arows11990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11990 = true := by
  rw [show D2M8K2.u11990 = KTree.node D2M8K2.u11986 (nat_lit 25572453) (nat_lit 1033252178) (nat_lit 0) D2M8K2.u11989 from rfl, allE_node, arows11986, irow11990, arows11989]
  all_goals rfl

theorem atot11990 : totK PD2M8K2 D2M8K2.u11990 = [0, 1260471347175, 3613222210633, 2120528863800, 185920517567, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11990 = KTree.node D2M8K2.u11986 (nat_lit 25572453) (nat_lit 1033252178) (nat_lit 0) D2M8K2.u11989 from rfl, totK_node, atot11986, atot11989]
  decide +kernel

theorem arows11999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11999 = true := by
  rw [show D2M8K2.u11999 = KTree.node D2M8K2.u11995 (nat_lit 25584250) (nat_lit 2230357837) (nat_lit 0) D2M8K2.u11998 from rfl, allE_node, arows11995, irow11999, arows11998]
  all_goals rfl

theorem atot11999 : totK PD2M8K2 D2M8K2.u11999 = [434114777975, 1965234727924, 2935741390212, 1545520569385, 229925721251, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11999 = KTree.node D2M8K2.u11995 (nat_lit 25584250) (nat_lit 2230357837) (nat_lit 0) D2M8K2.u11998 from rfl, totK_node, atot11995, atot11998]
  decide +kernel

theorem arows12006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12006 = true := by
  rw [show D2M8K2.u12006 = KTree.node D2M8K2.u12002 (nat_lit 25594891) (nat_lit 1765582230) (nat_lit 0) D2M8K2.u12005 from rfl, allE_node, arows12002, irow12006, arows12005]
  all_goals rfl

theorem atot12006 : totK PD2M8K2 D2M8K2.u12006 = [796180263521, 2787181728249, 2815067402311, 841593710280, 47219176148, 0, 0, 0] := by
  rw [show D2M8K2.u12006 = KTree.node D2M8K2.u12002 (nat_lit 25594891) (nat_lit 1765582230) (nat_lit 0) D2M8K2.u12005 from rfl, totK_node, atot12002, atot12005]
  decide +kernel

theorem arows12014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12014 = true := by
  rw [show D2M8K2.u12014 = KTree.node D2M8K2.u12010 (nat_lit 25608017) (nat_lit 1621084355) (nat_lit 0) D2M8K2.u12013 from rfl, allE_node, arows12010, irow12014, arows12013]
  all_goals rfl

theorem atot12014 : totK PD2M8K2 D2M8K2.u12014 = [428021878965, 2052972350654, 3116872180815, 1431512402438, 129990503414, 1310285577, 0, 0] := by
  rw [show D2M8K2.u12014 = KTree.node D2M8K2.u12010 (nat_lit 25608017) (nat_lit 1621084355) (nat_lit 0) D2M8K2.u12013 from rfl, totK_node, atot12010, atot12013]
  decide +kernel

theorem arows12021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12021 = true := by
  rw [show D2M8K2.u12021 = KTree.node D2M8K2.u12017 (nat_lit 25620345) (nat_lit 1677409657) (nat_lit 0) D2M8K2.u12020 from rfl, allE_node, arows12017, irow12021, arows12020]
  all_goals rfl

theorem atot12021 : totK PD2M8K2 D2M8K2.u12021 = [0, 1108139587782, 3352583931309, 2433328394045, 315500335587, 4931404646, 0, 0] := by
  rw [show D2M8K2.u12021 = KTree.node D2M8K2.u12017 (nat_lit 25620345) (nat_lit 1677409657) (nat_lit 0) D2M8K2.u12020 from rfl, totK_node, atot12017, atot12020]
  decide +kernel

theorem arows12033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12033 = true := by
  rw [show D2M8K2.u12033 = KTree.node D2M8K2.u12029 (nat_lit 25630658) (nat_lit 3637161467) (nat_lit 0) D2M8K2.u12032 from rfl, allE_node, arows12029, irow12033, arows12032]
  all_goals rfl

theorem atot12033 : totK PD2M8K2 D2M8K2.u12033 = [0, 837742047343, 2984156469771, 2718627077427, 569594700666, 23120318498, 0, 0] := by
  rw [show D2M8K2.u12033 = KTree.node D2M8K2.u12029 (nat_lit 25630658) (nat_lit 3637161467) (nat_lit 0) D2M8K2.u12032 from rfl, totK_node, atot12029, atot12032]
  decide +kernel

theorem arows12040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12040 = true := by
  rw [show D2M8K2.u12040 = KTree.node D2M8K2.u12036 (nat_lit 25641845) (nat_lit 2245008741) (nat_lit 0) D2M8K2.u12039 from rfl, allE_node, arows12036, irow12040, arows12039]
  all_goals rfl

theorem atot12040 : totK PD2M8K2 D2M8K2.u12040 = [0, 901955089524, 3072300934471, 2668948673303, 480896825701, 14354318128, 0, 0] := by
  rw [show D2M8K2.u12040 = KTree.node D2M8K2.u12036 (nat_lit 25641845) (nat_lit 2245008741) (nat_lit 0) D2M8K2.u12039 from rfl, totK_node, atot12036, atot12039]
  decide +kernel

theorem arows12048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12048 = true := by
  rw [show D2M8K2.u12048 = KTree.node D2M8K2.u12044 (nat_lit 25648861) (nat_lit 1268739303) (nat_lit 0) D2M8K2.u12047 from rfl, allE_node, arows12044, irow12048, arows12047]
  all_goals rfl

theorem atot12048 : totK PD2M8K2 D2M8K2.u12048 = [0, 382749107306, 2191414592138, 3311292703779, 1104210876958, 76733833513, 1310517177, 0] := by
  rw [show D2M8K2.u12048 = KTree.node D2M8K2.u12044 (nat_lit 25648861) (nat_lit 1268739303) (nat_lit 0) D2M8K2.u12047 from rfl, totK_node, atot12044, atot12047]
  decide +kernel

theorem arows12055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12055 = true := by
  rw [show D2M8K2.u12055 = KTree.node D2M8K2.u12051 (nat_lit 25662060) (nat_lit 3167593523) (nat_lit 0) D2M8K2.u12054 from rfl, allE_node, arows12051, irow12055, arows12054]
  all_goals rfl

theorem atot12055 : totK PD2M8K2 D2M8K2.u12055 = [0, 0, 1440149137048, 3715218647574, 1722743194821, 110423415199, 0, 0] := by
  rw [show D2M8K2.u12055 = KTree.node D2M8K2.u12051 (nat_lit 25662060) (nat_lit 3167593523) (nat_lit 0) D2M8K2.u12054 from rfl, totK_node, atot12051, atot12054]
  decide +kernel

theorem arows12064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12064 = true := by
  rw [show D2M8K2.u12064 = KTree.node D2M8K2.u12060 (nat_lit 25677223) (nat_lit 2355408521) (nat_lit 0) D2M8K2.u12063 from rfl, allE_node, arows12060, irow12064, arows12063]
  all_goals rfl

theorem atot12064 : totK PD2M8K2 D2M8K2.u12064 = [0, 772997982240, 2728250823585, 2866691484558, 890340157816, 50506400038, 0, 0] := by
  rw [show D2M8K2.u12064 = KTree.node D2M8K2.u12060 (nat_lit 25677223) (nat_lit 2355408521) (nat_lit 0) D2M8K2.u12063 from rfl, totK_node, atot12060, atot12063]
  decide +kernel

theorem arows12071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12071 = true := by
  rw [show D2M8K2.u12071 = KTree.node D2M8K2.u12067 (nat_lit 25684420) (nat_lit 2334999469) (nat_lit 0) D2M8K2.u12070 from rfl, allE_node, arows12067, irow12071, arows12070]
  all_goals rfl

theorem atot12071 : totK PD2M8K2 D2M8K2.u12071 = [0, 838094472952, 3033371522657, 2821944682319, 532990433798, 14410407170, 0, 0] := by
  rw [show D2M8K2.u12071 = KTree.node D2M8K2.u12067 (nat_lit 25684420) (nat_lit 2334999469) (nat_lit 0) D2M8K2.u12070 from rfl, totK_node, atot12067, atot12070]
  decide +kernel

theorem arows12079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12079 = true := by
  rw [show D2M8K2.u12079 = KTree.node D2M8K2.u12075 (nat_lit 25691662) (nat_lit 4009919491) (nat_lit 0) D2M8K2.u12078 from rfl, allE_node, arows12075, irow12079, arows12078]
  all_goals rfl

theorem atot12079 : totK PD2M8K2 D2M8K2.u12079 = [0, 798683396017, 2872474093055, 2815725459061, 638734924283, 23076361219, 0, 0] := by
  rw [show D2M8K2.u12079 = KTree.node D2M8K2.u12075 (nat_lit 25691662) (nat_lit 4009919491) (nat_lit 0) D2M8K2.u12078 from rfl, totK_node, atot12075, atot12078]
  decide +kernel

theorem arows12086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12086 = true := by
  rw [show D2M8K2.u12086 = KTree.node D2M8K2.u12082 (nat_lit 25760539) (nat_lit 2229081277) (nat_lit 0) D2M8K2.u12085 from rfl, allE_node, arows12082, irow12086, arows12085]
  all_goals rfl

theorem atot12086 : totK PD2M8K2 D2M8K2.u12086 = [0, 868590626247, 2904263268480, 2750696538140, 717267531860, 31349246366, 0, 0] := by
  rw [show D2M8K2.u12086 = KTree.node D2M8K2.u12082 (nat_lit 25760539) (nat_lit 2229081277) (nat_lit 0) D2M8K2.u12085 from rfl, totK_node, atot12082, atot12085]
  decide +kernel

end QECKChecks.D2M8K2
