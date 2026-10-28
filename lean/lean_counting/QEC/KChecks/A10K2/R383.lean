import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1532 = true := by
  decide +kernel

theorem tot1532 : totK PA10K2 A10K2.t1532 = [0, 0, 577484989024, 2090584760569, 2040494574104, 475002142117, 26877458525, 0, 0, 0] := by
  decide +kernel

theorem rows1533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1533 = true := by
  decide +kernel

theorem tot1533 : totK PA10K2 A10K2.t1533 = [0, 476523753575, 1501905832748, 1588315088655, 938979535292, 403997616430, 35751543300, 0, 0, 0] := by
  decide +kernel

theorem rows1534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1534 = true := by
  decide +kernel

theorem tot1534 : totK PA10K2 A10K2.t1534 = [0, 310356477484, 1565232169254, 2183767011277, 811087655609, 64908802480, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1535 = true := by
  decide +kernel

theorem tot1535 : totK PA10K2 A10K2.t1535 = [0, 0, 475234171327, 1828167056508, 1884669538716, 490956900476, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
