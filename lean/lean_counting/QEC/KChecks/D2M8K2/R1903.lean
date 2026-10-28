import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7612 = true := by
  decide +kernel

theorem tot7612 : totK PD2M8K2 D2M8K2.t7612 = [0, 0, 199633593617, 463685348999, 204702878649, 11949045446, 0, 0] := by
  decide +kernel

theorem rows7613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7613 = true := by
  decide +kernel

theorem tot7613 : totK PD2M8K2 D2M8K2.t7613 = [0, 0, 0, 325545767453, 446638119937, 75979687824, 1095107716, 0] := by
  decide +kernel

theorem rows7614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7614 = true := by
  decide +kernel

theorem tot7614 : totK PD2M8K2 D2M8K2.t7614 = [0, 90094024185, 124390884026, 215242508999, 343176248088, 94540414338, 3882006667, 0] := by
  decide +kernel

theorem rows7615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7615 = true := by
  decide +kernel

theorem tot7615 : totK PD2M8K2 D2M8K2.t7615 = [0, 162557680934, 477516903568, 239688458151, 11031163277, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
