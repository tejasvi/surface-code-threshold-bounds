import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1948 = true := by
  decide +kernel

theorem tot1948 : totK PD2M8K2 D2M8K2.t1948 = [0, 79747368630, 275164845076, 376270396709, 133515582037, 10740121073, 0, 0] := by
  decide +kernel

theorem rows1949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1949 = true := by
  decide +kernel

theorem tot1949 : totK PD2M8K2 D2M8K2.t1949 = [0, 172779360560, 464665565852, 256212709553, 20650127379, 0, 0, 0] := by
  decide +kernel

theorem rows1950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1950 = true := by
  decide +kernel

theorem tot1950 : totK PD2M8K2 D2M8K2.t1950 = [0, 173115031085, 472672910250, 239873324553, 12597559134, 0, 0, 0] := by
  decide +kernel

theorem rows1951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1951 = true := by
  decide +kernel

theorem tot1951 : totK PD2M8K2 D2M8K2.t1951 = [0, 0, 272431588442, 506853245077, 116857571964, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
