import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5612 = true := by
  decide +kernel

theorem tot5612 : totK PA10K2 A10K2.t5612 = [0, 0, 0, 284255375354, 1309653663151, 1858790347530, 978225206002, 162875024825, 5365973533, 0] := by
  decide +kernel

theorem rows5613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5613 = true := by
  decide +kernel

theorem tot5613 : totK PA10K2 A10K2.t5613 = [0, 0, 0, 452890738341, 1794975341831, 1877104301811, 400121745006, 16788721386, 0, 0] := by
  decide +kernel

theorem rows5614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5614 = true := by
  decide +kernel

theorem tot5614 : totK PA10K2 A10K2.t5614 = [0, 0, 0, 113147589240, 871659215251, 2038402374570, 1224020256265, 190652441267, 5528811039, 0] := by
  decide +kernel

theorem rows5615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5615 = true := by
  decide +kernel

theorem tot5615 : totK PA10K2 A10K2.t5615 = [0, 0, 304573652302, 1264208784152, 1946844531260, 1266990401418, 249451263984, 7872874101, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
