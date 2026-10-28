import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2816 = true := by
  decide +kernel

theorem tot2816 : totK PA10K2 A10K2.t2816 = [378919244585, 1567490444496, 2041267899995, 878927142247, 90485619246, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2817 = true := by
  decide +kernel

theorem tot2817 : totK PA10K2 A10K2.t2817 = [264625088314, 1420244782796, 2161903256230, 883908063344, 52738864247, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2818 = true := by
  decide +kernel

theorem tot2818 : totK PA10K2 A10K2.t2818 = [341298719405, 1288806331551, 1890098327772, 1094262801104, 217411388277, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2819 = true := by
  decide +kernel

theorem tot2819 : totK PA10K2 A10K2.t2819 = [458913958685, 1786087007085, 2076808592667, 671494485319, 39877718539, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
