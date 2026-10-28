import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13900 = true := by
  decide +kernel

theorem tot13900 : totK PD2M8K2 D2M8K2.t13900 = [187514830947, 464349754455, 245460692598, 23236262830, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13901 = true := by
  decide +kernel

theorem tot13901 : totK PD2M8K2 D2M8K2.t13901 = [184021707250, 459049161178, 235467744296, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13902 = true := by
  decide +kernel

theorem tot13902 : totK PD2M8K2 D2M8K2.t13902 = [37683970795, 340981060272, 435035124480, 82271507904, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13903 = true := by
  decide +kernel

theorem tot13903 : totK PD2M8K2 D2M8K2.t13903 = [0, 269274649390, 502683000129, 134182502719, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
