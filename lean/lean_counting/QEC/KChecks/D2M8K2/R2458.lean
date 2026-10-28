import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9832 = true := by
  decide +kernel

theorem tot9832 : totK PD2M8K2 D2M8K2.t9832 = [0, 0, 200450460319, 492510043131, 184512229515, 9482920370, 0, 0] := by
  decide +kernel

theorem rows9833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9833 = true := by
  decide +kernel

theorem tot9833 : totK PD2M8K2 D2M8K2.t9833 = [0, 164892027188, 446559664572, 255097301437, 37157627623, 2569691499, 0, 0] := by
  decide +kernel

theorem rows9834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9834 = true := by
  decide +kernel

theorem tot9834 : totK PD2M8K2 D2M8K2.t9834 = [0, 154042535696, 419535016622, 286758882834, 29875593964, 0, 0, 0] := by
  decide +kernel

theorem rows9835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9835 = true := by
  decide +kernel

theorem tot9835 : totK PD2M8K2 D2M8K2.t9835 = [0, 90854154917, 366361647981, 361387957627, 63586358813, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
