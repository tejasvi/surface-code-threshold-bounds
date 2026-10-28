import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1552 = true := by
  decide +kernel

theorem tot1552 : totK PA10K2 A10K2.t1552 = [0, 0, 513352896517, 1857453287237, 1921373563319, 601587164887, 49322181908, 0, 0, 0] := by
  decide +kernel

theorem rows1553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1553 = true := by
  decide +kernel

theorem tot1553 : totK PA10K2 A10K2.t1553 = [0, 0, 294981244009, 1431025499691, 2210886239630, 1012766417153, 80685291183, 0, 0, 0] := by
  decide +kernel

theorem rows1554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1554 = true := by
  decide +kernel

theorem tot1554 : totK PA10K2 A10K2.t1554 = [0, 0, 287377665471, 1148866839327, 1924572018597, 1328281889145, 245261732516, 6904928264, 0, 0] := by
  decide +kernel

theorem rows1555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1555 = true := by
  decide +kernel

theorem tot1555 : totK PA10K2 A10K2.t1555 = [0, 0, 509080381004, 1957458143063, 2127034517280, 548689323996, 19375727937, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
