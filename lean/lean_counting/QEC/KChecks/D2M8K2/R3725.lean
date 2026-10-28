import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14900 = true := by
  decide +kernel

theorem tot14900 : totK PD2M8K2 D2M8K2.t14900 = [0, 172248240994, 450143527306, 255513425622, 27474544470, 0, 0, 0] := by
  decide +kernel

theorem rows14901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14901 = true := by
  decide +kernel

theorem tot14901 : totK PD2M8K2 D2M8K2.t14901 = [0, 171626277997, 444190249167, 247322685555, 17480667719, 0, 0, 0] := by
  decide +kernel

theorem rows14902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14902 = true := by
  decide +kernel

theorem tot14902 : totK PD2M8K2 D2M8K2.t14902 = [0, 72130983226, 352825127650, 399618189197, 69618425258, 1075657031, 0, 0] := by
  decide +kernel

theorem rows14903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14903 = true := by
  decide +kernel

theorem tot14903 : totK PD2M8K2 D2M8K2.t14903 = [0, 18409415249, 282020994125, 459011211160, 110374290382, 3804183361, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
