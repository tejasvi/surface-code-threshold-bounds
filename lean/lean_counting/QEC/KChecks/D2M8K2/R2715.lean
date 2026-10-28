import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10860 = true := by
  decide +kernel

theorem tot10860 : totK PD2M8K2 D2M8K2.t10860 = [0, 0, 194030291417, 472890690413, 214788846701, 12835581599, 0, 0] := by
  decide +kernel

theorem rows10861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10861 = true := by
  decide +kernel

theorem tot10861 : totK PD2M8K2 D2M8K2.t10861 = [0, 0, 174912555571, 454969741107, 259139398673, 23282239808, 0, 0] := by
  decide +kernel

theorem rows10862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10862 = true := by
  decide +kernel

theorem tot10862 : totK PD2M8K2 D2M8K2.t10862 = [0, 0, 103563397318, 406197611395, 320050683270, 43763353611, 1162935789, 0] := by
  decide +kernel

theorem rows10863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10863 = true := by
  decide +kernel

theorem tot10863 : totK PD2M8K2 D2M8K2.t10863 = [0, 0, 0, 271792195587, 481017617452, 123104225679, 4232192998, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
