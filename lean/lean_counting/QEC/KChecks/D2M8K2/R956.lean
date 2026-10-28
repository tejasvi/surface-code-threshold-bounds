import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3824 = true := by
  decide +kernel

theorem tot3824 : totK PD2M8K2 D2M8K2.t3824 = [0, 0, 341076290777, 459617223318, 73367545169, 1053411165, 0, 0] := by
  decide +kernel

theorem rows3825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3825 = true := by
  decide +kernel

theorem tot3825 : totK PD2M8K2 D2M8K2.t3825 = [0, 130657817851, 356458239337, 290895465639, 75661159568, 3667207281, 0, 0] := by
  decide +kernel

theorem rows3826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3826 = true := by
  decide +kernel

theorem tot3826 : totK PD2M8K2 D2M8K2.t3826 = [0, 178892425509, 454844947062, 253289025002, 23373855263, 0, 0, 0] := by
  decide +kernel

theorem rows3827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3827 = true := by
  decide +kernel

theorem tot3827 : totK PD2M8K2 D2M8K2.t3827 = [70593750018, 205467963917, 367800889353, 243466149526, 22079952194, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
