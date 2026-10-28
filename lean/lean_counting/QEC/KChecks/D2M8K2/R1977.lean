import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7908 = true := by
  decide +kernel

theorem tot7908 : totK PD2M8K2 D2M8K2.t7908 = [0, 90468032897, 150699317451, 198749940993, 331204982441, 92199291644, 3667207281, 0] := by
  decide +kernel

theorem rows7909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7909 = true := by
  decide +kernel

theorem tot7909 : totK PD2M8K2 D2M8K2.t7909 = [0, 169076162321, 467465486542, 234887390281, 11038245751, 0, 0, 0] := by
  decide +kernel

theorem rows7910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7910 = true := by
  decide +kernel

theorem tot7910 : totK PD2M8K2 D2M8K2.t7910 = [0, 152883975043, 430904584451, 262977417370, 23156052482, 0, 0, 0] := by
  decide +kernel

theorem rows7911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7911 = true := by
  decide +kernel

theorem tot7911 : totK PD2M8K2 D2M8K2.t7911 = [0, 0, 270658472368, 506999603003, 106956729324, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
