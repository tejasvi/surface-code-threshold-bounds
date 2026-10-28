import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10644 = true := by
  decide +kernel

theorem tot10644 : totK PD2M8K2 D2M8K2.t10644 = [0, 0, 198782576997, 476182983836, 194270001963, 12052611869, 0, 0] := by
  decide +kernel

theorem rows10645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10645 = true := by
  decide +kernel

theorem tot10645 : totK PD2M8K2 D2M8K2.t10645 = [0, 175967501358, 451492579840, 266124508818, 28819713190, 0, 0, 0] := by
  decide +kernel

theorem rows10646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10646 = true := by
  decide +kernel

theorem tot10646 : totK PD2M8K2 D2M8K2.t10646 = [0, 189463955522, 461847722556, 234909437027, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows10647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10647 = true := by
  decide +kernel

theorem tot10647 : totK PD2M8K2 D2M8K2.t10647 = [0, 75207221427, 362824492378, 389960773735, 76212956708, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
