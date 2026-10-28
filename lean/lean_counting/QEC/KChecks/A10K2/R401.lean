import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1604 = true := by
  decide +kernel

theorem tot1604 : totK PA10K2 A10K2.t1604 = [0, 0, 479838864874, 1889197580185, 2108923420183, 607032289161, 32712955001, 0, 0, 0] := by
  decide +kernel

theorem rows1605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1605 = true := by
  decide +kernel

theorem tot1605 : totK PA10K2 A10K2.t1605 = [0, 560298200195, 1684668862433, 1580197812219, 738581513256, 277400261181, 30206063434, 0, 0, 0] := by
  decide +kernel

theorem rows1606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1606 = true := by
  decide +kernel

theorem tot1606 : totK PA10K2 A10K2.t1606 = [0, 0, 836658871864, 2124006397529, 1421198125703, 309190879691, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1607 = true := by
  decide +kernel

theorem tot1607 : totK PA10K2 A10K2.t1607 = [0, 369395021760, 1354895449295, 1832983162523, 1003545304390, 162132938648, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
