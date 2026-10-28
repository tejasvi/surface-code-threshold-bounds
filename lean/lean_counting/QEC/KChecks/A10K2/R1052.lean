import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4208 = true := by
  decide +kernel

theorem tot4208 : totK PA10K2 A10K2.t4208 = [0, 481271916829, 1725688582499, 1906363633260, 692394417487, 74577700312, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4209 = true := by
  decide +kernel

theorem tot4209 : totK PA10K2 A10K2.t4209 = [0, 296098192055, 1519997634262, 2134364197662, 800861476250, 58997332598, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4210 = true := by
  decide +kernel

theorem tot4210 : totK PA10K2 A10K2.t4210 = [0, 211669693007, 983547998150, 1925296742287, 1353058463243, 242112542772, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4211 = true := by
  decide +kernel

theorem tot4211 : totK PA10K2 A10K2.t4211 = [0, 473421418469, 1768222207969, 1953969921906, 553861253890, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
