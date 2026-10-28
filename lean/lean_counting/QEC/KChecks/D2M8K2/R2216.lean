import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8864 = true := by
  decide +kernel

theorem tot8864 : totK PD2M8K2 D2M8K2.t8864 = [0, 196947453112, 489146718277, 206658844358, 7807117139, 0, 0, 0] := by
  decide +kernel

theorem rows8865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8865 = true := by
  decide +kernel

theorem tot8865 : totK PD2M8K2 D2M8K2.t8865 = [0, 195783466949, 467914805577, 214327116067, 10751511312, 0, 0, 0] := by
  decide +kernel

theorem rows8866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8866 = true := by
  decide +kernel

theorem tot8866 : totK PD2M8K2 D2M8K2.t8866 = [75343529226, 223840189462, 373596367485, 223708737322, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows8867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8867 = true := by
  decide +kernel

theorem tot8867 : totK PD2M8K2 D2M8K2.t8867 = [173616173219, 444488102256, 278318101402, 28778737606, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
