import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8068 = true := by
  decide +kernel

theorem tot8068 : totK PD2M8K2 D2M8K2.t8068 = [0, 0, 0, 319211877968, 456821201610, 68893959993, 0, 0] := by
  decide +kernel

theorem rows8069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8069 = true := by
  decide +kernel

theorem tot8069 : totK PD2M8K2 D2M8K2.t8069 = [0, 0, 211870388303, 490907458771, 197164465835, 11166013279, 0, 0] := by
  decide +kernel

theorem rows8070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8070 = true := by
  decide +kernel

theorem tot8070 : totK PD2M8K2 D2M8K2.t8070 = [0, 0, 197580912486, 464199078459, 205025687132, 12243442891, 0, 0] := by
  decide +kernel

theorem rows8071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8071 = true := by
  decide +kernel

theorem tot8071 : totK PD2M8K2 D2M8K2.t8071 = [0, 0, 159047941997, 476064061948, 250550264612, 11686359316, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
