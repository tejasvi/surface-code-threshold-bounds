import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t524 = true := by
  decide +kernel

theorem tot524 : totK PA10K2 A10K2.t524 = [443195596967, 1430564309354, 1397496932980, 381632645935, 361891748843, 539208688183, 144939828619, 6239673734, 0, 0] := by
  decide +kernel

theorem rows525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t525 = true := by
  decide +kernel

theorem tot525 : totK PA10K2 A10K2.t525 = [369471400361, 1638284669488, 2062819783768, 744838209885, 59526954159, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t526 = true := by
  decide +kernel

theorem tot526 : totK PA10K2 A10K2.t526 = [0, 462333369585, 1827652834809, 1873995727755, 455336010998, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t527 = true := by
  decide +kernel

theorem tot527 : totK PA10K2 A10K2.t527 = [444966745009, 1588197841441, 1927833882018, 760243889570, 89854923792, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
