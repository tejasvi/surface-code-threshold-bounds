import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7896 = true := by
  decide +kernel

theorem tot7896 : totK PD2M8K2 D2M8K2.t7896 = [0, 0, 310090143772, 525543484232, 85939410236, 0, 0, 0] := by
  decide +kernel

theorem rows7897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7897 = true := by
  decide +kernel

theorem tot7897 : totK PD2M8K2 D2M8K2.t7897 = [0, 0, 176842000386, 489539124882, 197339142676, 6403024948, 0, 0] := by
  decide +kernel

theorem rows7898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7898 = true := by
  decide +kernel

theorem tot7898 : totK PD2M8K2 D2M8K2.t7898 = [0, 0, 174939826740, 462282663881, 218173925641, 12361325328, 0, 0] := by
  decide +kernel

theorem rows7899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7899 = true := by
  decide +kernel

theorem tot7899 : totK PD2M8K2 D2M8K2.t7899 = [0, 0, 63561706197, 359650206500, 375852469115, 53427096428, 1239866073, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
