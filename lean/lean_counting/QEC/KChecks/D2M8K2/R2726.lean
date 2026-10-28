import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10904 = true := by
  decide +kernel

theorem tot10904 : totK PD2M8K2 D2M8K2.t10904 = [0, 41656869575, 321605095560, 437189249546, 95749434839, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10905 = true := by
  decide +kernel

theorem tot10905 : totK PD2M8K2 D2M8K2.t10905 = [0, 70632388715, 353586549056, 433905937314, 53836541661, 0, 0, 0] := by
  decide +kernel

theorem rows10906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10906 = true := by
  decide +kernel

theorem tot10906 : totK PD2M8K2 D2M8K2.t10906 = [0, 160679670773, 439155591612, 278079603858, 29688315834, 0, 0, 0] := by
  decide +kernel

theorem rows10907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10907 = true := by
  decide +kernel

theorem tot10907 : totK PD2M8K2 D2M8K2.t10907 = [0, 193217774520, 484012329051, 224645673463, 10987934879, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
