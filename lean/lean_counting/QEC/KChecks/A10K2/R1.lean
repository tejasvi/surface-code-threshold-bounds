import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4 = true := by
  decide +kernel

theorem tot4 : totK PA10K2 A10K2.t4 = [280766130870, 1405773818139, 2050807360701, 827232818982, 65074462600, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5 = true := by
  decide +kernel

theorem tot5 : totK PA10K2 A10K2.t5 = [299321869460, 1114102887292, 1745622323400, 1193403427058, 233453279073, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6 = true := by
  decide +kernel

theorem tot6 : totK PA10K2 A10K2.t6 = [484635519347, 1896621915658, 2101677462930, 574454684056, 32078815772, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7 = true := by
  decide +kernel

theorem tot7 : totK PA10K2 A10K2.t7 = [0, 756012467106, 2254746617119, 1716481956725, 301883491609, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
