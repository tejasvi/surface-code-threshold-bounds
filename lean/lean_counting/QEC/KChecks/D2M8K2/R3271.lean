import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13084 = true := by
  decide +kernel

theorem tot13084 : totK PD2M8K2 D2M8K2.t13084 = [0, 23480092369, 274173016226, 413109954322, 187867342404, 21400436502, 0, 0] := by
  decide +kernel

theorem rows13085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13085 = true := by
  decide +kernel

theorem tot13085 : totK PD2M8K2 D2M8K2.t13085 = [0, 0, 196268760669, 487691932915, 204133115945, 7994456143, 0, 0] := by
  decide +kernel

theorem rows13086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13086 = true := by
  decide +kernel

theorem tot13086 : totK PD2M8K2 D2M8K2.t13086 = [0, 89943055225, 266696941170, 370956296757, 175683793431, 8214505460, 0, 0] := by
  decide +kernel

theorem rows13087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13087 = true := by
  decide +kernel

theorem tot13087 : totK PD2M8K2 D2M8K2.t13087 = [0, 171415482183, 445615836045, 267295118393, 29347462205, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
