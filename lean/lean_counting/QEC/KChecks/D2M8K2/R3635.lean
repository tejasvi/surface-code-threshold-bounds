import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14540 = true := by
  decide +kernel

theorem tot14540 : totK PD2M8K2 D2M8K2.t14540 = [71007842519, 243982938784, 391574553190, 190183027508, 8187600046, 0, 0, 0] := by
  decide +kernel

theorem rows14541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14541 = true := by
  decide +kernel

theorem tot14541 : totK PD2M8K2 D2M8K2.t14541 = [182639300068, 459680231108, 249951061991, 22981289911, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14542 = true := by
  decide +kernel

theorem tot14542 : totK PD2M8K2 D2M8K2.t14542 = [164634488024, 473827358965, 250457110491, 13779823240, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14543 = true := by
  decide +kernel

theorem tot14543 : totK PD2M8K2 D2M8K2.t14543 = [0, 280455035132, 495598493996, 114691358272, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
