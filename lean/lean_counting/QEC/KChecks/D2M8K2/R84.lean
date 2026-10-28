import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t336 = true := by
  decide +kernel

theorem tot336 : totK PD2M8K2 D2M8K2.t336 = [0, 70642649624, 257455662842, 371797273596, 164575931969, 7877424857, 0, 0] := by
  decide +kernel

theorem rows337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t337 = true := by
  decide +kernel

theorem tot337 : totK PD2M8K2 D2M8K2.t337 = [0, 182097221416, 453075981626, 267123729348, 27780178356, 0, 0, 0] := by
  decide +kernel

theorem rows338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t338 = true := by
  decide +kernel

theorem tot338 : totK PD2M8K2 D2M8K2.t338 = [0, 171653650330, 458781511324, 246394619658, 13937131162, 0, 0, 0] := by
  decide +kernel

theorem rows339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t339 = true := by
  decide +kernel

theorem tot339 : totK PD2M8K2 D2M8K2.t339 = [0, 0, 279831681280, 484766070298, 123432659868, 4009909289, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
