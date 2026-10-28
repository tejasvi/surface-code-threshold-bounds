import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6440 = true := by
  decide +kernel

theorem tot6440 : totK PA10K2 A10K2.t6440 = [0, 126429703929, 777223281827, 1825675307968, 1633957950489, 460587946606, 30780440178, 0, 0, 0] := by
  decide +kernel

theorem rows6441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6441 = true := by
  decide +kernel

theorem tot6441 : totK PA10K2 A10K2.t6441 = [0, 566029012784, 1957529638291, 2013867516287, 588945076631, 36767934768, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6442 = true := by
  decide +kernel

theorem tot6442 : totK PA10K2 A10K2.t6442 = [0, 121142009141, 1038658383530, 2193446652919, 1452155395078, 252839366459, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6443 = true := by
  decide +kernel

theorem tot6443 : totK PA10K2 A10K2.t6443 = [0, 0, 537898020747, 1963319143970, 2119022052958, 555907782622, 18183661895, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
