import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13156 = true := by
  decide +kernel

theorem tot13156 : totK PD2M8K2 D2M8K2.t13156 = [0, 95189083643, 396053495280, 339570687088, 43663961612, 0, 0, 0] := by
  decide +kernel

theorem rows13157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13157 = true := by
  decide +kernel

theorem tot13157 : totK PD2M8K2 D2M8K2.t13157 = [0, 0, 290490627832, 502009596030, 97129209485, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13158 = true := by
  decide +kernel

theorem tot13158 : totK PD2M8K2 D2M8K2.t13158 = [0, 173305329320, 435865434440, 282105839834, 32517241621, 0, 0, 0] := by
  decide +kernel

theorem rows13159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13159 = true := by
  decide +kernel

theorem tot13159 : totK PD2M8K2 D2M8K2.t13159 = [0, 176098695668, 474209679309, 240576500292, 15720084590, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
