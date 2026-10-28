import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7940 = true := by
  decide +kernel

theorem tot7940 : totK PD2M8K2 D2M8K2.t7940 = [0, 0, 175862963285, 453706717912, 250270226875, 22828318141, 0, 0] := by
  decide +kernel

theorem rows7941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7941 = true := by
  decide +kernel

theorem tot7941 : totK PD2M8K2 D2M8K2.t7941 = [0, 0, 106099855469, 432500548449, 306756362173, 27005494330, 0, 0] := by
  decide +kernel

theorem rows7942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7942 = true := by
  decide +kernel

theorem tot7942 : totK PD2M8K2 D2M8K2.t7942 = [0, 0, 0, 305600602933, 472940202458, 92590515335, 1095107716, 0] := by
  decide +kernel

theorem rows7943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7943 = true := by
  decide +kernel

theorem tot7943 : totK PD2M8K2 D2M8K2.t7943 = [0, 0, 167804228932, 383405161784, 257977715023, 82415938502, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
