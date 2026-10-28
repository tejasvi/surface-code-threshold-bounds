import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8188 = true := by
  decide +kernel

theorem tot8188 : totK PA10K2 A10K2.t8188 = [0, 0, 0, 0, 274197112624, 1336210262082, 1941439761068, 1081326229417, 183557542231, 6439430839] := by
  decide +kernel

theorem rows8189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8189 = true := by
  decide +kernel

theorem tot8189 : totK PA10K2 A10K2.t8189 = [0, 0, 0, 0, 604543636357, 2038420584786, 1888257219798, 409545121383, 11163036971, 0] := by
  decide +kernel

theorem rows8190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8190 = true := by
  decide +kernel

theorem tot8190 : totK PA10K2 A10K2.t8190 = [0, 0, 0, 0, 0, 730770031927, 2165355295640, 1605931915666, 252112768718, 6021244195] := by
  decide +kernel

theorem rows8191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8191 = true := by
  decide +kernel

theorem tot8191 : totK PA10K2 A10K2.t8191 = [0, 0, 0, 0, 0, 405797140217, 1720603415300, 2057473931515, 709076559954, 54997142734] := by
  decide +kernel

end QECKChecks.A10K2
