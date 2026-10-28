import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9888 = true := by
  decide +kernel

theorem tot9888 : totK PD2M8K2 D2M8K2.t9888 = [0, 0, 0, 313759308130, 461409217160, 85945734532, 1095107716, 0] := by
  decide +kernel

theorem rows9889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9889 = true := by
  decide +kernel

theorem tot9889 : totK PD2M8K2 D2M8K2.t9889 = [0, 174456625603, 372444996889, 133192504167, 129211361521, 70797398904, 3882006667, 0] := by
  decide +kernel

theorem rows9890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9890 = true := by
  decide +kernel

theorem tot9890 : totK PD2M8K2 D2M8K2.t9890 = [0, 155548146664, 443447160520, 255197587606, 18182990193, 0, 0, 0] := by
  decide +kernel

theorem rows9891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9891 = true := by
  decide +kernel

theorem tot9891 : totK PD2M8K2 D2M8K2.t9891 = [0, 89411507079, 337756178568, 384969493761, 88574195178, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
