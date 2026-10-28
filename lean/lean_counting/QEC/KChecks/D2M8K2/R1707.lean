import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6828 = true := by
  decide +kernel

theorem tot6828 : totK PD2M8K2 D2M8K2.t6828 = [0, 180062671018, 470648790205, 250900960865, 18252358503, 0, 0, 0] := by
  decide +kernel

theorem rows6829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6829 = true := by
  decide +kernel

theorem tot6829 : totK PD2M8K2 D2M8K2.t6829 = [0, 0, 321558584945, 466203001188, 73789909035, 1021600638, 0, 0] := by
  decide +kernel

theorem rows6830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6830 = true := by
  decide +kernel

theorem tot6830 : totK PD2M8K2 D2M8K2.t6830 = [0, 122765833322, 359847856837, 304016824355, 76287771931, 3552795014, 0, 0] := by
  decide +kernel

theorem rows6831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6831 = true := by
  decide +kernel

theorem tot6831 : totK PD2M8K2 D2M8K2.t6831 = [0, 175474541388, 449995134597, 260591746911, 25454216038, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
