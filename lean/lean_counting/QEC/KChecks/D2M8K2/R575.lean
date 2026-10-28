import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2300 = true := by
  decide +kernel

theorem tot2300 : totK PD2M8K2 D2M8K2.t2300 = [0, 20021956556, 176331326710, 452841614475, 242259077563, 17433533548, 0, 0] := by
  decide +kernel

theorem rows2301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2301 = true := by
  decide +kernel

theorem tot2301 : totK PD2M8K2 D2M8K2.t2301 = [0, 160987572430, 445168024975, 279794148112, 30024746217, 0, 0, 0] := by
  decide +kernel

theorem rows2302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2302 = true := by
  decide +kernel

theorem tot2302 : totK PD2M8K2 D2M8K2.t2302 = [0, 207994249007, 480484986621, 210587000770, 10486696241, 0, 0, 0] := by
  decide +kernel

theorem rows2303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2303 = true := by
  decide +kernel

theorem tot2303 : totK PD2M8K2 D2M8K2.t2303 = [0, 37745533432, 287346556344, 392317882306, 178487724125, 21400436502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
