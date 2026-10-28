import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4788 = true := by
  decide +kernel

theorem tot4788 : totK PD2M8K2 D2M8K2.t4788 = [0, 123340586977, 427103256507, 310897933596, 29552914007, 0, 0, 0] := by
  decide +kernel

theorem rows4789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4789 = true := by
  decide +kernel

theorem tot4789 : totK PD2M8K2 D2M8K2.t4789 = [0, 0, 277510575510, 519298063248, 103071696777, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4790 = true := by
  decide +kernel

theorem tot4790 : totK PD2M8K2 D2M8K2.t4790 = [0, 173887923212, 444438968659, 285771866052, 33970700489, 0, 0, 0] := by
  decide +kernel

theorem rows4791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4791 = true := by
  decide +kernel

theorem tot4791 : totK PD2M8K2 D2M8K2.t4791 = [0, 191546907961, 484167241204, 228859679941, 12532735358, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
