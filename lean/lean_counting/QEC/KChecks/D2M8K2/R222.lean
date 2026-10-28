import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t888 = true := by
  decide +kernel

theorem tot888 : totK PD2M8K2 D2M8K2.t888 = [0, 119440198663, 362790228408, 324871257356, 84966399567, 3518381706, 0, 0] := by
  decide +kernel

theorem rows889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t889 = true := by
  decide +kernel

theorem tot889 : totK PD2M8K2 D2M8K2.t889 = [0, 170367005676, 446359757174, 261608290082, 27398359950, 0, 0, 0] := by
  decide +kernel

theorem rows890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t890 = true := by
  decide +kernel

theorem tot890 : totK PD2M8K2 D2M8K2.t890 = [0, 146118275952, 458388096753, 293333706471, 23459543939, 0, 0, 0] := by
  decide +kernel

theorem rows891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t891 = true := by
  decide +kernel

theorem tot891 : totK PD2M8K2 D2M8K2.t891 = [0, 0, 219765972386, 491704815712, 159967656059, 4901932702, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
