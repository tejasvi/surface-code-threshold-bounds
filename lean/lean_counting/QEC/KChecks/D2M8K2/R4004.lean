import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16016 = true := by
  decide +kernel

theorem tot16016 : totK PD2M8K2 D2M8K2.t16016 = [0, 0, 0, 207669029158, 488320616700, 169014795949, 5380947575, 0] := by
  decide +kernel

theorem rows16017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16017 = true := by
  decide +kernel

theorem tot16017 : totK PD2M8K2 D2M8K2.t16017 = [0, 0, 0, 0, 317953032792, 444088599157, 70949003374, 1217496766] := by
  decide +kernel

theorem rows16018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16018 = true := by
  decide +kernel

theorem tot16018 : totK PD2M8K2 D2M8K2.t16018 = [0, 0, 0, 157035112370, 437152420997, 283792623246, 23280427564, 0] := by
  decide +kernel

theorem rows16019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16019 = true := by
  decide +kernel

theorem tot16019 : totK PD2M8K2 D2M8K2.t16019 = [0, 0, 0, 256359559474, 507079796881, 153346961809, 1910420280, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
