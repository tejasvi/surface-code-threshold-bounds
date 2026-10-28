import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2544 = true := by
  decide +kernel

theorem tot2544 : totK PD2M8K2 D2M8K2.t2544 = [0, 188491465709, 464073198033, 237140114351, 14525611387, 0, 0, 0] := by
  decide +kernel

theorem rows2545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2545 = true := by
  decide +kernel

theorem tot2545 : totK PD2M8K2 D2M8K2.t2545 = [0, 57916323603, 364481500380, 377305922118, 59920917045, 1053411165, 0, 0] := by
  decide +kernel

theorem rows2546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2546 = true := by
  decide +kernel

theorem tot2546 : totK PD2M8K2 D2M8K2.t2546 = [0, 48210584066, 294216238093, 411261456463, 98233928601, 3667207281, 0, 0] := by
  decide +kernel

theorem rows2547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2547 = true := by
  decide +kernel

theorem tot2547 : totK PD2M8K2 D2M8K2.t2547 = [0, 186095645275, 458178096909, 243635176019, 20872377286, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
