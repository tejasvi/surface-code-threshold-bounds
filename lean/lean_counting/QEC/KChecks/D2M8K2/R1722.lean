import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6888 = true := by
  decide +kernel

theorem tot6888 : totK PD2M8K2 D2M8K2.t6888 = [0, 174199877314, 478054689160, 243400335865, 16220436538, 0, 0, 0] := by
  decide +kernel

theorem rows6889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6889 = true := by
  decide +kernel

theorem tot6889 : totK PD2M8K2 D2M8K2.t6889 = [0, 179654455608, 465602866613, 249082541955, 20632281267, 0, 0, 0] := by
  decide +kernel

theorem rows6890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6890 = true := by
  decide +kernel

theorem tot6890 : totK PD2M8K2 D2M8K2.t6890 = [0, 156799562566, 447308481286, 267506835353, 24405634669, 0, 0, 0] := by
  decide +kernel

theorem rows6891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6891 = true := by
  decide +kernel

theorem tot6891 : totK PD2M8K2 D2M8K2.t6891 = [0, 0, 247443001500, 483117640380, 128807496560, 4879840392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
