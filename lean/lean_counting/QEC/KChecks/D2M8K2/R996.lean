import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3984 = true := by
  decide +kernel

theorem tot3984 : totK PD2M8K2 D2M8K2.t3984 = [0, 0, 190243876183, 488112413484, 209699641179, 4878316567, 0, 0] := by
  decide +kernel

theorem rows3985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3985 = true := by
  decide +kernel

theorem tot3985 : totK PD2M8K2 D2M8K2.t3985 = [0, 137975527160, 353112293820, 281512162602, 111276176420, 6804944647, 0, 0] := by
  decide +kernel

theorem rows3986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3986 = true := by
  decide +kernel

theorem tot3986 : totK PD2M8K2 D2M8K2.t3986 = [0, 165723408565, 434344361739, 276441605151, 29851081663, 0, 0, 0] := by
  decide +kernel

theorem rows3987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3987 = true := by
  decide +kernel

theorem tot3987 : totK PD2M8K2 D2M8K2.t3987 = [0, 111075905096, 421022349752, 328147348041, 32771484037, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
