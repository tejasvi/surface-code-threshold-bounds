import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1712 = true := by
  decide +kernel

theorem tot1712 : totK PD2M8K2 D2M8K2.t1712 = [0, 0, 169621453135, 479189794776, 234916716548, 12688117470, 0, 0] := by
  decide +kernel

theorem rows1713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1713 = true := by
  decide +kernel

theorem tot1713 : totK PD2M8K2 D2M8K2.t1713 = [0, 0, 191803029584, 475483386487, 225225602378, 13182197566, 0, 0] := by
  decide +kernel

theorem rows1714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1714 = true := by
  decide +kernel

theorem tot1714 : totK PD2M8K2 D2M8K2.t1714 = [0, 0, 180026672369, 455894994096, 258914696214, 18916154790, 0, 0] := by
  decide +kernel

theorem rows1715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1715 = true := by
  decide +kernel

theorem tot1715 : totK PD2M8K2 D2M8K2.t1715 = [0, 0, 141297699709, 446007408162, 288008155882, 21740333600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
