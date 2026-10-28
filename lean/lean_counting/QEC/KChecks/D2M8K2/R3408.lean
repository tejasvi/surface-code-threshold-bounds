import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13632 = true := by
  decide +kernel

theorem tot13632 : totK PD2M8K2 D2M8K2.t13632 = [0, 0, 308265261113, 483258027607, 80081726989, 0, 0, 0] := by
  decide +kernel

theorem rows13633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13633 = true := by
  decide +kernel

theorem tot13633 : totK PD2M8K2 D2M8K2.t13633 = [176791677709, 383523406934, 135579361620, 119129131125, 75135337308, 3882006667, 0, 0] := by
  decide +kernel

theorem rows13634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13634 = true := by
  decide +kernel

theorem tot13634 : totK PD2M8K2 D2M8K2.t13634 = [155561835999, 449422149980, 255592992119, 18182990193, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13635 = true := by
  decide +kernel

theorem tot13635 : totK PD2M8K2 D2M8K2.t13635 = [89411507079, 337179034983, 384286509321, 91255700045, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
