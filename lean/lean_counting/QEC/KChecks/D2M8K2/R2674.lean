import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10696 = true := by
  decide +kernel

theorem tot10696 : totK PD2M8K2 D2M8K2.t10696 = [0, 0, 239938760006, 516900668793, 164134054643, 4118414865, 0, 0] := by
  decide +kernel

theorem rows10697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10697 = true := by
  decide +kernel

theorem tot10697 : totK PD2M8K2 D2M8K2.t10697 = [0, 0, 162283880281, 443661739665, 284146466652, 28610727168, 0, 0] := by
  decide +kernel

theorem rows10698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10698 = true := by
  decide +kernel

theorem tot10698 : totK PD2M8K2 D2M8K2.t10698 = [0, 0, 131816429019, 442839606499, 303679076439, 24722256561, 0, 0] := by
  decide +kernel

theorem rows10699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10699 = true := by
  decide +kernel

theorem tot10699 : totK PD2M8K2 D2M8K2.t10699 = [0, 0, 0, 257654766812, 501408369771, 137464481028, 7316020427, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
