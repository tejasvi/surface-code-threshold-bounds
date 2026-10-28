import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4508 = true := by
  decide +kernel

theorem tot4508 : totK PA10K2 A10K2.t4508 = [0, 397862999098, 1224399152930, 1602359348734, 1230167762375, 405795144798, 31276155898, 0, 0, 0] := by
  decide +kernel

theorem rows4509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4509 = true := by
  decide +kernel

theorem tot4509 : totK PA10K2 A10K2.t4509 = [0, 70674273105, 968563077182, 2130545271368, 1262789124300, 174781276336, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4510 = true := by
  decide +kernel

theorem tot4510 : totK PA10K2 A10K2.t4510 = [0, 584442978767, 1964973479711, 1817742333635, 462235265458, 26491486257, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4511 = true := by
  decide +kernel

theorem tot4511 : totK PA10K2 A10K2.t4511 = [0, 215434075875, 1266609650829, 2255634696580, 1156035861183, 113678790612, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
