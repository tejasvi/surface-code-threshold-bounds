import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6672 = true := by
  decide +kernel

theorem tot6672 : totK PD2M8K2 D2M8K2.t6672 = [0, 51570335955, 345211113344, 412102434513, 79079755712, 1096505104, 0, 0] := by
  decide +kernel

theorem rows6673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6673 = true := by
  decide +kernel

theorem tot6673 : totK PD2M8K2 D2M8K2.t6673 = [0, 18256998497, 271346971870, 481878480058, 123302885029, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6674 = true := by
  decide +kernel

theorem tot6674 : totK PD2M8K2 D2M8K2.t6674 = [0, 188103579982, 457719388225, 243836046527, 21071697240, 0, 0, 0] := by
  decide +kernel

theorem rows6675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6675 = true := by
  decide +kernel

theorem tot6675 : totK PD2M8K2 D2M8K2.t6675 = [0, 134436510344, 447097455347, 306640957674, 26169249844, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
