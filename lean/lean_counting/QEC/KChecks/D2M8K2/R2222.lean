import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8888 = true := by
  decide +kernel

theorem tot8888 : totK PD2M8K2 D2M8K2.t8888 = [0, 176035710390, 471294994199, 251448591340, 12697795161, 0, 0, 0] := by
  decide +kernel

theorem rows8889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8889 = true := by
  decide +kernel

theorem tot8889 : totK PD2M8K2 D2M8K2.t8889 = [0, 88827548222, 375981808016, 365576415287, 81176792975, 10444649207, 0, 0] := by
  decide +kernel

theorem rows8890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8890 = true := by
  decide +kernel

theorem tot8890 : totK PD2M8K2 D2M8K2.t8890 = [0, 0, 170417457108, 449754685684, 247851215789, 17508088435, 0, 0] := by
  decide +kernel

theorem rows8891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8891 = true := by
  decide +kernel

theorem tot8891 : totK PD2M8K2 D2M8K2.t8891 = [0, 19809922038, 191085706583, 457729232925, 210453229255, 8969136212, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
