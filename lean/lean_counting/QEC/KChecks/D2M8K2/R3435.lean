import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13740 = true := by
  decide +kernel

theorem tot13740 : totK PD2M8K2 D2M8K2.t13740 = [0, 69426390014, 227942172993, 400203173920, 183244906449, 12482056447, 0, 0] := by
  decide +kernel

theorem rows13741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13741 = true := by
  decide +kernel

theorem tot13741 : totK PD2M8K2 D2M8K2.t13741 = [0, 190725087147, 477986305890, 205839464372, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows13742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13742 = true := by
  decide +kernel

theorem tot13742 : totK PD2M8K2 D2M8K2.t13742 = [0, 158217167705, 456068850516, 255353434420, 14852339619, 0, 0, 0] := by
  decide +kernel

theorem rows13743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13743 = true := by
  decide +kernel

theorem tot13743 : totK PD2M8K2 D2M8K2.t13743 = [0, 0, 275681074337, 495015082350, 110488233887, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
