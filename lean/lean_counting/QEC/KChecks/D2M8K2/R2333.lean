import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9332 = true := by
  decide +kernel

theorem tot9332 : totK PD2M8K2 D2M8K2.t9332 = [0, 164659483850, 467999566946, 250446618996, 12597559134, 0, 0, 0] := by
  decide +kernel

theorem rows9333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9333 = true := by
  decide +kernel

theorem tot9333 : totK PD2M8K2 D2M8K2.t9333 = [0, 0, 269563380866, 513297503332, 109081300308, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9334 = true := by
  decide +kernel

theorem tot9334 : totK PD2M8K2 D2M8K2.t9334 = [0, 54618809271, 229883763988, 407232823171, 165912662944, 11986244008, 0, 0] := by
  decide +kernel

theorem rows9335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9335 = true := by
  decide +kernel

theorem tot9335 : totK PD2M8K2 D2M8K2.t9335 = [0, 187543218977, 464206771243, 225435313643, 16192212756, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
