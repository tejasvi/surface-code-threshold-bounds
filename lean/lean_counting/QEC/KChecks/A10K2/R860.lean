import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3440 = true := by
  decide +kernel

theorem tot3440 : totK PA10K2 A10K2.t3440 = [0, 0, 0, 551077358557, 1763921068165, 1777614128033, 722493344660, 136048661388, 6239673734, 0] := by
  decide +kernel

theorem rows3441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3441 = true := by
  decide +kernel

theorem tot3441 : totK PA10K2 A10K2.t3441 = [0, 0, 0, 226369335867, 1430292571359, 2309659111185, 995153336377, 81276885117, 0, 0] := by
  decide +kernel

theorem rows3442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3442 = true := by
  decide +kernel

theorem tot3442 : totK PA10K2 A10K2.t3442 = [0, 0, 0, 0, 514952257575, 1885762792455, 1953231481996, 551376352198, 35586898073, 0] := by
  decide +kernel

theorem rows3443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3443 = true := by
  decide +kernel

theorem tot3443 : totK PA10K2 A10K2.t3443 = [0, 0, 0, 0, 438568618422, 1751494342406, 1923133425775, 531179767292, 32523532663, 0] := by
  decide +kernel

end QECKChecks.A10K2
