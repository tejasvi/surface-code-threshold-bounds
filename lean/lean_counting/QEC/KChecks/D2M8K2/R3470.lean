import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13880 = true := by
  decide +kernel

theorem tot13880 : totK PD2M8K2 D2M8K2.t13880 = [0, 0, 222869286799, 465635123091, 174565916547, 9633262574, 0, 0] := by
  decide +kernel

theorem rows13881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13881 = true := by
  decide +kernel

theorem tot13881 : totK PD2M8K2 D2M8K2.t13881 = [0, 110652807981, 347030975093, 328164490267, 82857924519, 3472187823, 0, 0] := by
  decide +kernel

theorem rows13882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13882 = true := by
  decide +kernel

theorem tot13882 : totK PD2M8K2 D2M8K2.t13882 = [0, 182253552292, 484410459732, 235188709354, 13350560930, 0, 0, 0] := by
  decide +kernel

theorem rows13883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13883 = true := by
  decide +kernel

theorem tot13883 : totK PD2M8K2 D2M8K2.t13883 = [0, 88522936701, 373098245541, 346399839848, 58956468486, 1053411165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
