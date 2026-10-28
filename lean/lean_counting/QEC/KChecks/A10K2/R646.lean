import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2584 = true := by
  decide +kernel

theorem tot2584 : totK PA10K2 A10K2.t2584 = [0, 151274968355, 932312712076, 2018057013336, 1335185572327, 207631459116, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows2585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2585 = true := by
  decide +kernel

theorem tot2585 : totK PA10K2 A10K2.t2585 = [113616355882, 613643492568, 1634625309919, 1927795181827, 757483144718, 69713971004, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2586 = true := by
  decide +kernel

theorem tot2586 : totK PA10K2 A10K2.t2586 = [453058992472, 1795284895428, 1903268033071, 480623217146, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2587 = true := by
  decide +kernel

theorem tot2587 : totK PA10K2 A10K2.t2587 = [129948670344, 858345418043, 1803975452843, 1374189131150, 351201770947, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
