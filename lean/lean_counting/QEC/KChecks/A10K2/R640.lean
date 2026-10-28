import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2560 = true := by
  decide +kernel

theorem tot2560 : totK PA10K2 A10K2.t2560 = [305225869305, 1547668406188, 2160088253099, 814438147781, 64912000717, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2561 = true := by
  decide +kernel

theorem tot2561 : totK PA10K2 A10K2.t2561 = [0, 478899265903, 1790331082096, 1861879816653, 490517721420, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2562 = true := by
  decide +kernel

theorem tot2562 : totK PA10K2 A10K2.t2562 = [481968697395, 1708918661660, 1861110019103, 668747362942, 73372343113, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2563 = true := by
  decide +kernel

theorem tot2563 : totK PA10K2 A10K2.t2563 = [297981042541, 1502483617586, 2124604962059, 802261013276, 51330830718, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
