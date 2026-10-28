import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14504 = true := by
  decide +kernel

theorem tot14504 : totK PD2M8K2 D2M8K2.t14504 = [176600050142, 401355231749, 231971871537, 95667245618, 6775760191, 0, 0, 0] := by
  decide +kernel

theorem rows14505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14505 = true := by
  decide +kernel

theorem tot14505 : totK PD2M8K2 D2M8K2.t14505 = [180465534664, 457822728624, 260377038550, 18438013872, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14506 = true := by
  decide +kernel

theorem tot14506 : totK PD2M8K2 D2M8K2.t14506 = [88945508586, 365241437463, 371527179547, 69494739664, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14507 = true := by
  decide +kernel

theorem tot14507 : totK PD2M8K2 D2M8K2.t14507 = [0, 249025352241, 495040709820, 158585064237, 8470662040, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
