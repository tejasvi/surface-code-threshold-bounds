import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t516 = true := by
  decide +kernel

theorem tot516 : totK PD2M8K2 D2M8K2.t516 = [0, 0, 287748473545, 517609340424, 92742881157, 1062926506, 0, 0] := by
  decide +kernel

theorem rows517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t517 = true := by
  decide +kernel

theorem tot517 : totK PD2M8K2 D2M8K2.t517 = [0, 171217150621, 370731564543, 257108010405, 74180149642, 3783381897, 0, 0] := by
  decide +kernel

theorem rows518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t518 = true := by
  decide +kernel

theorem tot518 : totK PD2M8K2 D2M8K2.t518 = [0, 156198403932, 443378564062, 280208502655, 29442763128, 0, 0, 0] := by
  decide +kernel

theorem rows519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t519 = true := by
  decide +kernel

theorem tot519 : totK PD2M8K2 D2M8K2.t519 = [0, 92616578666, 381378839690, 362085831556, 56592922121, 1240621948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
