import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t320 = true := by
  decide +kernel

theorem tot320 : totK PA10K2 A10K2.t320 = [0, 445631118586, 1762033644253, 1986106824452, 555979507011, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t321 = true := by
  decide +kernel

theorem tot321 : totK PA10K2 A10K2.t321 = [0, 144091739800, 942934714056, 1922595381675, 1447399561388, 364123086872, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t322 = true := by
  decide +kernel

theorem tot322 : totK PA10K2 A10K2.t322 = [0, 240806066827, 1142675694501, 1952791935276, 1230004205192, 201231138401, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t323 = true := by
  decide +kernel

theorem tot323 : totK PA10K2 A10K2.t323 = [0, 344146364017, 1513839906168, 2007955025203, 766695654763, 61022968793, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
