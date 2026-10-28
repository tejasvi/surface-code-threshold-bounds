import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13140 = true := by
  decide +kernel

theorem tot13140 : totK PD2M8K2 D2M8K2.t13140 = [0, 0, 84362010335, 385672956892, 336540248351, 50199165153, 1239866073, 0] := by
  decide +kernel

theorem rows13141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13141 = true := by
  decide +kernel

theorem tot13141 : totK PD2M8K2 D2M8K2.t13141 = [0, 0, 19982995165, 332827166413, 458600443967, 58346740081, 0, 0] := by
  decide +kernel

theorem rows13142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13142 = true := by
  decide +kernel

theorem tot13142 : totK PD2M8K2 D2M8K2.t13142 = [0, 0, 190080092563, 456708064316, 248530499683, 22850596136, 0, 0] := by
  decide +kernel

theorem rows13143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13143 = true := by
  decide +kernel

theorem tot13143 : totK PD2M8K2 D2M8K2.t13143 = [0, 0, 188963586176, 487244698699, 212282938322, 11311631362, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
