import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6308 = true := by
  decide +kernel

theorem tot6308 : totK PD2M8K2 D2M8K2.t6308 = [0, 87191050473, 408571989610, 357884934477, 42716528464, 0, 0, 0] := by
  decide +kernel

theorem rows6309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6309 = true := by
  decide +kernel

theorem tot6309 : totK PD2M8K2 D2M8K2.t6309 = [0, 0, 221205604006, 487300940307, 171465286119, 8423393484, 0, 0] := by
  decide +kernel

theorem rows6310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6310 = true := by
  decide +kernel

theorem tot6310 : totK PD2M8K2 D2M8K2.t6310 = [0, 104494763718, 347775957059, 340720314911, 83857359751, 3462014130, 0, 0] := by
  decide +kernel

theorem rows6311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6311 = true := by
  decide +kernel

theorem tot6311 : totK PD2M8K2 D2M8K2.t6311 = [0, 197351985121, 460678473050, 203061520882, 12420044233, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
