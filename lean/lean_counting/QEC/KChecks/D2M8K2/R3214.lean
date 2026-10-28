import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12856 = true := by
  decide +kernel

theorem tot12856 : totK PD2M8K2 D2M8K2.t12856 = [0, 166834398016, 441192451945, 274658572615, 29978038796, 0, 0, 0] := by
  decide +kernel

theorem rows12857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12857 = true := by
  decide +kernel

theorem tot12857 : totK PD2M8K2 D2M8K2.t12857 = [0, 205825815501, 488270028118, 209329972945, 10465033296, 0, 0, 0] := by
  decide +kernel

theorem rows12858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12858 = true := by
  decide +kernel

theorem tot12858 : totK PD2M8K2 D2M8K2.t12858 = [0, 26464483550, 269994308765, 412750347276, 186748410656, 21391863750, 0, 0] := by
  decide +kernel

theorem rows12859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12859 = true := by
  decide +kernel

theorem tot12859 : totK PD2M8K2 D2M8K2.t12859 = [0, 0, 201945183233, 477417246036, 201806946108, 7983871751, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
