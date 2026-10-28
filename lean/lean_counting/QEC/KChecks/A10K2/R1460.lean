import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5840 = true := by
  decide +kernel

theorem tot5840 : totK PA10K2 A10K2.t5840 = [0, 0, 0, 982062480022, 2433280107267, 1220706752386, 107172403957, 0, 0, 0] := by
  decide +kernel

theorem rows5841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5841 = true := by
  decide +kernel

theorem tot5841 : totK PA10K2 A10K2.t5841 = [0, 0, 458520426296, 1528318068088, 1709666388627, 885510426089, 193933203403, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5842 = true := by
  decide +kernel

theorem tot5842 : totK PA10K2 A10K2.t5842 = [0, 0, 0, 720589650118, 2211852687986, 1626458493605, 210889388540, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5843 = true := by
  decide +kernel

theorem tot5843 : totK PA10K2 A10K2.t5843 = [0, 0, 0, 488503614371, 1802648263649, 1921909358281, 477075090296, 31222411477, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
