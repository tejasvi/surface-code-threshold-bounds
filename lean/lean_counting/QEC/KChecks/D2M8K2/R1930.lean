import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7720 = true := by
  decide +kernel

theorem tot7720 : totK PD2M8K2 D2M8K2.t7720 = [0, 0, 0, 122009032585, 411386490250, 324729136125, 33928674619, 0] := by
  decide +kernel

theorem rows7721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7721 = true := by
  decide +kernel

theorem tot7721 : totK PD2M8K2 D2M8K2.t7721 = [0, 0, 0, 211796211285, 489815034481, 187263535168, 5795556757, 0] := by
  decide +kernel

theorem rows7722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7722 = true := by
  decide +kernel

theorem tot7722 : totK PD2M8K2 D2M8K2.t7722 = [0, 0, 0, 216495767928, 492680150038, 184292824152, 6705308190, 0] := by
  decide +kernel

theorem rows7723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7723 = true := by
  decide +kernel

theorem tot7723 : totK PD2M8K2 D2M8K2.t7723 = [0, 0, 0, 175272978706, 455956090824, 253888216338, 23241079343, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
