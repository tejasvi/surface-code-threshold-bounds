import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13776 = true := by
  decide +kernel

theorem tot13776 : totK PD2M8K2 D2M8K2.t13776 = [163226047787, 450810349382, 284407581615, 30321150294, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13777 = true := by
  decide +kernel

theorem tot13777 : totK PD2M8K2 D2M8K2.t13777 = [195171909925, 481238718747, 223786401967, 11637544544, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13778 = true := by
  decide +kernel

theorem tot13778 : totK PD2M8K2 D2M8K2.t13778 = [34527251780, 276094551039, 407154407985, 184309683787, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows13779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13779 = true := by
  decide +kernel

theorem tot13779 : totK PD2M8K2 D2M8K2.t13779 = [0, 205368287002, 485029181076, 205881501535, 7994456143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
