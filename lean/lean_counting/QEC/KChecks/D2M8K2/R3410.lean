import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13640 = true := by
  decide +kernel

theorem tot13640 : totK PD2M8K2 D2M8K2.t13640 = [50771107978, 222614857265, 419002971960, 208690596637, 10703994771, 0, 0, 0] := by
  decide +kernel

theorem rows13641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13641 = true := by
  decide +kernel

theorem tot13641 : totK PD2M8K2 D2M8K2.t13641 = [188070900190, 467636336002, 241690428838, 21817690983, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13642 = true := by
  decide +kernel

theorem tot13642 : totK PD2M8K2 D2M8K2.t13642 = [173943437419, 466272511707, 241296755578, 13615052294, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13643 = true := by
  decide +kernel

theorem tot13643 : totK PD2M8K2 D2M8K2.t13643 = [0, 283678985287, 509272930861, 110765554038, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
