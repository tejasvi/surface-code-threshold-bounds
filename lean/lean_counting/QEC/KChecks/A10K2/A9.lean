import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A8

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows5214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5214 = true := by
  rw [show A10K2.u5214 = KTree.node A10K2.u5212 (nat_lit 84144519) (nat_lit 14471687564) (nat_lit 0) A10K2.u5213 from rfl, allE_node, arows5212, irow5214, arows5213]
  all_goals rfl

theorem atot5214 : totK PA10K2 A10K2.u5214 = [0, 0, 1224623886484, 5235792810971, 7917956680567, 4726650109988, 893273674844, 39854233058, 0, 0] := by
  rw [show A10K2.u5214 = KTree.node A10K2.u5212 (nat_lit 84144519) (nat_lit 14471687564) (nat_lit 0) A10K2.u5213 from rfl, totK_node, atot5212, atot5213]
  decide +kernel

theorem arows5217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5217 = true := by
  rw [show A10K2.u5217 = KTree.node A10K2.u5215 (nat_lit 84154924) (nat_lit 11945750104) (nat_lit 0) A10K2.u5216 from rfl, allE_node, arows5215, irow5217, arows5216]
  all_goals rfl

theorem atot5217 : totK PA10K2 A10K2.u5217 = [0, 0, 1166753603554, 5371402757499, 7822806671012, 3889495113081, 639505490904, 30831673886, 0, 0] := by
  rw [show A10K2.u5217 = KTree.node A10K2.u5215 (nat_lit 84154924) (nat_lit 11945750104) (nat_lit 0) A10K2.u5216 from rfl, totK_node, atot5215, atot5216]
  decide +kernel

theorem arows5221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5221 = true := by
  rw [show A10K2.u5221 = KTree.node A10K2.u5219 (nat_lit 84176284) (nat_lit 5066976535) (nat_lit 0) A10K2.u5220 from rfl, allE_node, arows5219, irow5221, arows5220]
  all_goals rfl

theorem atot5221 : totK PA10K2 A10K2.u5221 = [0, 0, 740599976690, 4384022690724, 8219420854920, 5109091561510, 873765273228, 40736193832, 0, 0] := by
  rw [show A10K2.u5221 = KTree.node A10K2.u5219 (nat_lit 84176284) (nat_lit 5066976535) (nat_lit 0) A10K2.u5220 from rfl, totK_node, atot5219, atot5220]
  decide +kernel

theorem arows5224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5224 = true := by
  rw [show A10K2.u5224 = KTree.node A10K2.u5222 (nat_lit 84187137) (nat_lit 10498121125) (nat_lit 0) A10K2.u5223 from rfl, allE_node, arows5222, irow5224, arows5223]
  all_goals rfl

theorem atot5224 : totK PA10K2 A10K2.u5224 = [0, 0, 0, 1260589649870, 5595759973009, 7596690368413, 3522839066560, 606613734588, 30605747850, 0] := by
  rw [show A10K2.u5224 = KTree.node A10K2.u5222 (nat_lit 84187137) (nat_lit 10498121125) (nat_lit 0) A10K2.u5223 from rfl, totK_node, atot5222, atot5223]
  decide +kernel

theorem arows5229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5229 = true := by
  rw [show A10K2.u5229 = KTree.node A10K2.u5227 (nat_lit 84209075) (nat_lit 9293053464) (nat_lit 0) A10K2.u5228 from rfl, allE_node, arows5227, irow5229, arows5228]
  all_goals rfl

theorem atot5229 : totK PA10K2 A10K2.u5229 = [0, 0, 797092040211, 3753731111250, 6672485418873, 5704793950946, 2031271434590, 240688322013, 5528811039, 0] := by
  rw [show A10K2.u5229 = KTree.node A10K2.u5227 (nat_lit 84209075) (nat_lit 9293053464) (nat_lit 0) A10K2.u5228 from rfl, totK_node, atot5227, atot5228]
  decide +kernel

theorem arows5232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5232 = true := by
  rw [show A10K2.u5232 = KTree.node A10K2.u5230 (nat_lit 84290053) (nat_lit 6791634080) (nat_lit 0) A10K2.u5231 from rfl, allE_node, arows5230, irow5232, arows5231]
  all_goals rfl

theorem atot5232 : totK PA10K2 A10K2.u5232 = [0, 0, 1049658106254, 4746215216192, 7650688171517, 4538222339402, 814087203474, 36865889447, 0, 0] := by
  rw [show A10K2.u5232 = KTree.node A10K2.u5230 (nat_lit 84290053) (nat_lit 6791634080) (nat_lit 0) A10K2.u5231 from rfl, totK_node, atot5230, atot5231]
  decide +kernel

theorem arows5236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5236 = true := by
  rw [show A10K2.u5236 = KTree.node A10K2.u5234 (nat_lit 84312621) (nat_lit 5533269284) (nat_lit 0) A10K2.u5235 from rfl, allE_node, arows5234, irow5236, arows5235]
  all_goals rfl

theorem atot5236 : totK PA10K2 A10K2.u5236 = [0, 0, 208565205755, 3132560267846, 8049150742053, 6094976328990, 1232809468982, 51145658493, 0, 0] := by
  rw [show A10K2.u5236 = KTree.node A10K2.u5234 (nat_lit 84312621) (nat_lit 5533269284) (nat_lit 0) A10K2.u5235 from rfl, totK_node, atot5234, atot5235]
  decide +kernel

theorem arows5239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5239 = true := by
  rw [show A10K2.u5239 = KTree.node A10K2.u5237 (nat_lit 84334867) (nat_lit 10408587183) (nat_lit 0) A10K2.u5238 from rfl, allE_node, arows5237, irow5239, arows5238]
  all_goals rfl

theorem atot5239 : totK PA10K2 A10K2.u5239 = [0, 0, 806416526819, 3685018908624, 6633425091305, 5635639231804, 1916660857011, 222927555409, 5676195732, 0] := by
  rw [show A10K2.u5239 = KTree.node A10K2.u5237 (nat_lit 84334867) (nat_lit 10408587183) (nat_lit 0) A10K2.u5238 from rfl, totK_node, atot5237, atot5238]
  decide +kernel

theorem arows5247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5247 = true := by
  rw [show A10K2.u5247 = KTree.node A10K2.u5245 (nat_lit 84369443) (nat_lit 2377785388) (nat_lit 0) A10K2.u5246 from rfl, allE_node, arows5245, irow5247, arows5246]
  all_goals rfl

theorem atot5247 : totK PA10K2 A10K2.u5247 = [0, 0, 1077743967298, 5220002848167, 8375597748331, 4613529750910, 749089501867, 32166696177, 0, 0] := by
  rw [show A10K2.u5247 = KTree.node A10K2.u5245 (nat_lit 84369443) (nat_lit 2377785388) (nat_lit 0) A10K2.u5246 from rfl, totK_node, atot5245, atot5246]
  decide +kernel

theorem arows5250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5250 = true := by
  rw [show A10K2.u5250 = KTree.node A10K2.u5248 (nat_lit 84937490) (nat_lit 11191514312) (nat_lit 0) A10K2.u5249 from rfl, allE_node, arows5248, irow5250, arows5249]
  all_goals rfl

theorem atot5250 : totK PA10K2 A10K2.u5250 = [0, 833436429740, 3868561300215, 6489592863268, 5152626040478, 2479573606020, 536617490092, 29687484142, 0, 0] := by
  rw [show A10K2.u5250 = KTree.node A10K2.u5248 (nat_lit 84937490) (nat_lit 11191514312) (nat_lit 0) A10K2.u5249 from rfl, totK_node, atot5248, atot5249]
  decide +kernel

theorem arows5254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5254 = true := by
  rw [show A10K2.u5254 = KTree.node A10K2.u5252 (nat_lit 84956389) (nat_lit 7023573905) (nat_lit 0) A10K2.u5253 from rfl, allE_node, arows5252, irow5254, arows5253]
  all_goals rfl

theorem atot5254 : totK PA10K2 A10K2.u5254 = [0, 1322336744556, 5774543847369, 8060203632286, 3679423535121, 438414471036, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5254 = KTree.node A10K2.u5252 (nat_lit 84956389) (nat_lit 7023573905) (nat_lit 0) A10K2.u5253 from rfl, totK_node, atot5252, atot5253]
  decide +kernel

theorem arows5257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5257 = true := by
  rw [show A10K2.u5257 = KTree.node A10K2.u5255 (nat_lit 84970276) (nat_lit 14096986228) (nat_lit 0) A10K2.u5256 from rfl, allE_node, arows5255, irow5257, arows5256]
  all_goals rfl

theorem atot5257 : totK PA10K2 A10K2.u5257 = [0, 0, 1290254576017, 5527065731307, 7828144056280, 3792241634734, 623658832448, 30650496230, 0, 0] := by
  rw [show A10K2.u5257 = KTree.node A10K2.u5255 (nat_lit 84970276) (nat_lit 14096986228) (nat_lit 0) A10K2.u5256 from rfl, totK_node, atot5255, atot5256]
  decide +kernel

theorem arows5262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5262 = true := by
  rw [show A10K2.u5262 = KTree.node A10K2.u5260 (nat_lit 84990056) (nat_lit 11384882569) (nat_lit 0) A10K2.u5261 from rfl, allE_node, arows5260, irow5262, arows5261]
  all_goals rfl

theorem atot5262 : totK PA10K2 A10K2.u5262 = [0, 303055287478, 2161863293347, 6233286946731, 7404198422088, 2838009491845, 287720742877, 5546304973, 0, 0] := by
  rw [show A10K2.u5262 = KTree.node A10K2.u5260 (nat_lit 84990056) (nat_lit 11384882569) (nat_lit 0) A10K2.u5261 from rfl, totK_node, atot5260, atot5261]
  decide +kernel

theorem arows5265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5265 = true := by
  rw [show A10K2.u5265 = KTree.node A10K2.u5263 (nat_lit 85015230) (nat_lit 7706808837) (nat_lit 128) A10K2.u5264 from rfl, allE_node, arows5263, irow5265, arows5264]
  all_goals rfl

theorem atot5265 : totK PA10K2 A10K2.u5265 = [0, 1239322164441, 5600373639273, 8038963640148, 3914499279617, 585305986507, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5265 = KTree.node A10K2.u5263 (nat_lit 85015230) (nat_lit 7706808837) (nat_lit 128) A10K2.u5264 from rfl, totK_node, atot5263, atot5264]
  decide +kernel

theorem arows5269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5269 = true := by
  rw [show A10K2.u5269 = KTree.node A10K2.u5267 (nat_lit 85044053) (nat_lit 6626725597) (nat_lit 0) A10K2.u5268 from rfl, allE_node, arows5267, irow5269, arows5268]
  all_goals rfl

theorem atot5269 : totK PA10K2 A10K2.u5269 = [0, 0, 1617286935841, 6265243676035, 7490778545634, 3249759096228, 507581678895, 31082886609, 0, 0] := by
  rw [show A10K2.u5269 = KTree.node A10K2.u5267 (nat_lit 85044053) (nat_lit 6626725597) (nat_lit 0) A10K2.u5268 from rfl, totK_node, atot5267, atot5268]
  decide +kernel

theorem arows5272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5272 = true := by
  rw [show A10K2.u5272 = KTree.node A10K2.u5270 (nat_lit 85056161) (nat_lit 6567288826) (nat_lit 0) A10K2.u5271 from rfl, allE_node, arows5270, irow5272, arows5271]
  all_goals rfl

theorem atot5272 : totK PA10K2 A10K2.u5272 = [0, 762214156616, 3603174500563, 6563973655061, 5731834475097, 2135633427325, 245885793701, 6121173289, 0, 0] := by
  rw [show A10K2.u5272 = KTree.node A10K2.u5270 (nat_lit 85056161) (nat_lit 6567288826) (nat_lit 0) A10K2.u5271 from rfl, totK_node, atot5270, atot5271]
  decide +kernel

theorem arows5278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5278 = true := by
  rw [show A10K2.u5278 = KTree.node A10K2.u5276 (nat_lit 85076744) (nat_lit 11812794897) (nat_lit 0) A10K2.u5277 from rfl, allE_node, arows5276, irow5278, arows5277]
  all_goals rfl

theorem atot5278 : totK PA10K2 A10K2.u5278 = [0, 927277137081, 4436030723037, 7527240351569, 5039280631205, 1093440449462, 62600422739, 0, 0, 0] := by
  rw [show A10K2.u5278 = KTree.node A10K2.u5276 (nat_lit 85076744) (nat_lit 11812794897) (nat_lit 0) A10K2.u5277 from rfl, totK_node, atot5276, atot5277]
  decide +kernel

theorem arows5281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5281 = true := by
  rw [show A10K2.u5281 = KTree.node A10K2.u5279 (nat_lit 85088534) (nat_lit 8471380067) (nat_lit 0) A10K2.u5280 from rfl, allE_node, arows5279, irow5281, arows5280]
  all_goals rfl

theorem atot5281 : totK PA10K2 A10K2.u5281 = [0, 564595576905, 3902404839334, 7967263772909, 5495991556862, 1104226626291, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u5281 = KTree.node A10K2.u5279 (nat_lit 85088534) (nat_lit 8471380067) (nat_lit 0) A10K2.u5280 from rfl, totK_node, atot5279, atot5280]
  decide +kernel

theorem arows5285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5285 = true := by
  rw [show A10K2.u5285 = KTree.node A10K2.u5283 (nat_lit 85116627) (nat_lit 10592099614) (nat_lit 0) A10K2.u5284 from rfl, allE_node, arows5283, irow5285, arows5284]
  all_goals rfl

theorem atot5285 : totK PA10K2 A10K2.u5285 = [0, 0, 1488785624692, 6151316092021, 7855075019608, 2977778412003, 355384936875, 6354482628, 0, 0] := by
  rw [show A10K2.u5285 = KTree.node A10K2.u5283 (nat_lit 85116627) (nat_lit 10592099614) (nat_lit 0) A10K2.u5284 from rfl, totK_node, atot5283, atot5284]
  decide +kernel

theorem arows5288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5288 = true := by
  rw [show A10K2.u5288 = KTree.node A10K2.u5286 (nat_lit 85201668) (nat_lit 12442994009) (nat_lit 0) A10K2.u5287 from rfl, allE_node, arows5286, irow5288, arows5287]
  all_goals rfl

theorem atot5288 : totK PA10K2 A10K2.u5288 = [0, 0, 1197992297126, 5341737736233, 7821409771853, 3998601570299, 647185226311, 30818366867, 0, 0] := by
  rw [show A10K2.u5288 = KTree.node A10K2.u5286 (nat_lit 85201668) (nat_lit 12442994009) (nat_lit 0) A10K2.u5287 from rfl, totK_node, atot5286, atot5287]
  decide +kernel

theorem arows5293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5293 = true := by
  rw [show A10K2.u5293 = KTree.node A10K2.u5291 (nat_lit 85222180) (nat_lit 13375170513) (nat_lit 0) A10K2.u5292 from rfl, allE_node, arows5291, irow5293, arows5292]
  all_goals rfl

theorem atot5293 : totK PA10K2 A10K2.u5293 = [0, 0, 1047464425060, 5190752282995, 8209991348670, 4293436825400, 606956802234, 13207830636, 0, 0] := by
  rw [show A10K2.u5293 = KTree.node A10K2.u5291 (nat_lit 85222180) (nat_lit 13375170513) (nat_lit 0) A10K2.u5292 from rfl, totK_node, atot5291, atot5292]
  decide +kernel

theorem arows5296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5296 = true := by
  rw [show A10K2.u5296 = KTree.node A10K2.u5294 (nat_lit 85277482) (nat_lit 11789152397) (nat_lit 0) A10K2.u5295 from rfl, allE_node, arows5294, irow5296, arows5295]
  all_goals rfl

theorem atot5296 : totK PA10K2 A10K2.u5296 = [0, 0, 1236692518767, 5541859397985, 8014680678051, 3909497416855, 570640603064, 31452573850, 0, 0] := by
  rw [show A10K2.u5296 = KTree.node A10K2.u5294 (nat_lit 85277482) (nat_lit 11789152397) (nat_lit 0) A10K2.u5295 from rfl, totK_node, atot5294, atot5295]
  decide +kernel

theorem arows5300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5300 = true := by
  rw [show A10K2.u5300 = KTree.node A10K2.u5298 (nat_lit 85330953) (nat_lit 9732766126) (nat_lit 0) A10K2.u5299 from rfl, allE_node, arows5298, irow5300, arows5299]
  all_goals rfl

theorem atot5300 : totK PA10K2 A10K2.u5300 = [0, 0, 1037922489557, 4939255198349, 7847023295439, 4334704613688, 741491390288, 36429366174, 0, 0] := by
  rw [show A10K2.u5300 = KTree.node A10K2.u5298 (nat_lit 85330953) (nat_lit 9732766126) (nat_lit 0) A10K2.u5299 from rfl, totK_node, atot5298, atot5299]
  decide +kernel

theorem arows5303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5303 = true := by
  rw [show A10K2.u5303 = KTree.node A10K2.u5301 (nat_lit 85343387) (nat_lit 9966385584) (nat_lit 0) A10K2.u5302 from rfl, allE_node, arows5301, irow5303, arows5302]
  all_goals rfl

theorem atot5303 : totK PA10K2 A10K2.u5303 = [0, 0, 1213557433736, 5446275363220, 7845721277902, 3771029463122, 587792368273, 31003444686, 0, 0] := by
  rw [show A10K2.u5303 = KTree.node A10K2.u5301 (nat_lit 85343387) (nat_lit 9966385584) (nat_lit 0) A10K2.u5302 from rfl, totK_node, atot5301, atot5302]
  decide +kernel

theorem arows5310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5310 = true := by
  rw [show A10K2.u5310 = KTree.node A10K2.u5308 (nat_lit 85363541) (nat_lit 6800300424) (nat_lit 0) A10K2.u5309 from rfl, allE_node, arows5308, irow5310, arows5309]
  all_goals rfl

theorem atot5310 : totK PA10K2 A10K2.u5310 = [0, 0, 0, 2375147461148, 7835024711242, 6756909674820, 1558788037000, 93893887517, 0, 0] := by
  rw [show A10K2.u5310 = KTree.node A10K2.u5308 (nat_lit 85363541) (nat_lit 6800300424) (nat_lit 0) A10K2.u5309 from rfl, totK_node, atot5308, atot5309]
  decide +kernel

theorem arows5313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5313 = true := by
  rw [show A10K2.u5313 = KTree.node A10K2.u5311 (nat_lit 85383968) (nat_lit 12125212889) (nat_lit 0) A10K2.u5312 from rfl, allE_node, arows5311, irow5313, arows5312]
  all_goals rfl

theorem atot5313 : totK PA10K2 A10K2.u5313 = [0, 842822735057, 3289402214160, 4332201855111, 3941999995624, 4181584268784, 1935588021967, 291068676346, 6354482628, 0] := by
  rw [show A10K2.u5313 = KTree.node A10K2.u5311 (nat_lit 85383968) (nat_lit 12125212889) (nat_lit 0) A10K2.u5312 from rfl, totK_node, atot5311, atot5312]
  decide +kernel

theorem arows5317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5317 = true := by
  rw [show A10K2.u5317 = KTree.node A10K2.u5315 (nat_lit 85477659) (nat_lit 9127738902) (nat_lit 0) A10K2.u5316 from rfl, allE_node, arows5315, irow5317, arows5316]
  all_goals rfl

theorem atot5317 : totK PA10K2 A10K2.u5317 = [0, 1046063391514, 4981298131920, 7933834357702, 4529628676704, 795361442221, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u5317 = KTree.node A10K2.u5315 (nat_lit 85477659) (nat_lit 9127738902) (nat_lit 0) A10K2.u5316 from rfl, totK_node, atot5315, atot5316]
  decide +kernel

theorem arows5320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5320 = true := by
  rw [show A10K2.u5320 = KTree.node A10K2.u5318 (nat_lit 85491258) (nat_lit 11265855181) (nat_lit 0) A10K2.u5319 from rfl, allE_node, arows5318, irow5320, arows5319]
  all_goals rfl

theorem atot5320 : totK PA10K2 A10K2.u5320 = [0, 316555443509, 2838355710091, 7541875519867, 7169745923063, 1984866745035, 123195634356, 0, 0, 0] := by
  rw [show A10K2.u5320 = KTree.node A10K2.u5318 (nat_lit 85491258) (nat_lit 11265855181) (nat_lit 0) A10K2.u5319 from rfl, totK_node, atot5318, atot5319]
  decide +kernel

theorem arows5325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5325 = true := by
  rw [show A10K2.u5325 = KTree.node A10K2.u5323 (nat_lit 85510299) (nat_lit 9875192451) (nat_lit 0) A10K2.u5324 from rfl, allE_node, arows5323, irow5325, arows5324]
  all_goals rfl

theorem atot5325 : totK PA10K2 A10K2.u5325 = [0, 0, 1043558097640, 4998936488115, 7862509996033, 4293449210695, 766115605130, 36196801203, 0, 0] := by
  rw [show A10K2.u5325 = KTree.node A10K2.u5323 (nat_lit 85510299) (nat_lit 9875192451) (nat_lit 0) A10K2.u5324 from rfl, totK_node, atot5323, atot5324]
  decide +kernel

theorem arows5328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5328 = true := by
  rw [show A10K2.u5328 = KTree.node A10K2.u5326 (nat_lit 85659100) (nat_lit 1788465909) (nat_lit 0) A10K2.u5327 from rfl, allE_node, arows5326, irow5328, arows5327]
  all_goals rfl

theorem atot5328 : totK PA10K2 A10K2.u5328 = [0, 1068376898294, 4836326762824, 7671281235563, 4962623544628, 1216273794027, 81297804047, 0, 0, 0] := by
  rw [show A10K2.u5328 = KTree.node A10K2.u5326 (nat_lit 85659100) (nat_lit 1788465909) (nat_lit 0) A10K2.u5327 from rfl, totK_node, atot5326, atot5327]
  decide +kernel

theorem arows5332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5332 = true := by
  rw [show A10K2.u5332 = KTree.node A10K2.u5330 (nat_lit 85680631) (nat_lit 14886314268) (nat_lit 0) A10K2.u5331 from rfl, allE_node, arows5330, irow5332, arows5331]
  all_goals rfl

theorem atot5332 : totK PA10K2 A10K2.u5332 = [0, 1175483150104, 5371822121159, 8261783959879, 4578454239098, 726739663256, 20425520299, 0, 0, 0] := by
  rw [show A10K2.u5332 = KTree.node A10K2.u5330 (nat_lit 85680631) (nat_lit 14886314268) (nat_lit 0) A10K2.u5331 from rfl, totK_node, atot5330, atot5331]
  decide +kernel

theorem arows5335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5335 = true := by
  rw [show A10K2.u5335 = KTree.node A10K2.u5333 (nat_lit 85690888) (nat_lit 14167382902) (nat_lit 0) A10K2.u5334 from rfl, allE_node, arows5333, irow5335, arows5334]
  all_goals rfl

theorem atot5335 : totK PA10K2 A10K2.u5335 = [0, 0, 1540040201336, 6169271854410, 8047264927876, 3570532309220, 423285870820, 6904928264, 0, 0] := by
  rw [show A10K2.u5335 = KTree.node A10K2.u5333 (nat_lit 85690888) (nat_lit 14167382902) (nat_lit 0) A10K2.u5334 from rfl, totK_node, atot5333, atot5334]
  decide +kernel

theorem arows5341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5341 = true := by
  rw [show A10K2.u5341 = KTree.node A10K2.u5339 (nat_lit 85713156) (nat_lit 9852200984) (nat_lit 0) A10K2.u5340 from rfl, allE_node, arows5339, irow5341, arows5340]
  all_goals rfl

theorem atot5341 : totK PA10K2 A10K2.u5341 = [0, 0, 1283884004239, 5825068388454, 8439926429419, 4078864685201, 436745199701, 7047025452, 0, 0] := by
  rw [show A10K2.u5341 = KTree.node A10K2.u5339 (nat_lit 85713156) (nat_lit 9852200984) (nat_lit 0) A10K2.u5340 from rfl, totK_node, atot5339, atot5340]
  decide +kernel

theorem arows5344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5344 = true := by
  rw [show A10K2.u5344 = KTree.node A10K2.u5342 (nat_lit 85723201) (nat_lit 10335345372) (nat_lit 0) A10K2.u5343 from rfl, allE_node, arows5342, irow5344, arows5343]
  all_goals rfl

theorem atot5344 : totK PA10K2 A10K2.u5344 = [0, 0, 842822735057, 4198940219384, 7498436388657, 5402392762596, 1327665732746, 86443380410, 0, 0] := by
  rw [show A10K2.u5344 = KTree.node A10K2.u5342 (nat_lit 85723201) (nat_lit 10335345372) (nat_lit 0) A10K2.u5343 from rfl, totK_node, atot5342, atot5343]
  decide +kernel

theorem arows5348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5348 = true := by
  rw [show A10K2.u5348 = KTree.node A10K2.u5346 (nat_lit 85743892) (nat_lit 13357073411) (nat_lit 0) A10K2.u5347 from rfl, allE_node, arows5346, irow5348, arows5347]
  all_goals rfl

theorem atot5348 : totK PA10K2 A10K2.u5348 = [0, 0, 1362618835023, 5940666272758, 8178581443322, 3627629866704, 464430239046, 11152205789, 0, 0] := by
  rw [show A10K2.u5348 = KTree.node A10K2.u5346 (nat_lit 85743892) (nat_lit 13357073411) (nat_lit 0) A10K2.u5347 from rfl, totK_node, atot5346, atot5347]
  decide +kernel

theorem arows5351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5351 = true := by
  rw [show A10K2.u5351 = KTree.node A10K2.u5349 (nat_lit 85756066) (nat_lit 8179549556) (nat_lit 0) A10K2.u5350 from rfl, allE_node, arows5349, irow5351, arows5350]
  all_goals rfl

theorem atot5351 : totK PA10K2 A10K2.u5351 = [0, 0, 0, 1635237165666, 6502154423842, 7981131664182, 3094233467905, 363798182042, 7007974415, 0] := by
  rw [show A10K2.u5351 = KTree.node A10K2.u5349 (nat_lit 85756066) (nat_lit 8179549556) (nat_lit 0) A10K2.u5350 from rfl, totK_node, atot5349, atot5350]
  decide +kernel

theorem arows5356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5356 = true := by
  rw [show A10K2.u5356 = KTree.node A10K2.u5354 (nat_lit 85782052) (nat_lit 8435417318) (nat_lit 0) A10K2.u5355 from rfl, allE_node, arows5354, irow5356, arows5355]
  all_goals rfl

theorem atot5356 : totK PA10K2 A10K2.u5356 = [0, 0, 780629253406, 4285154389951, 7994792656249, 5547635027474, 1087335712125, 54252526246, 0, 0] := by
  rw [show A10K2.u5356 = KTree.node A10K2.u5354 (nat_lit 85782052) (nat_lit 8435417318) (nat_lit 0) A10K2.u5355 from rfl, totK_node, atot5354, atot5355]
  decide +kernel

theorem arows5359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5359 = true := by
  rw [show A10K2.u5359 = KTree.node A10K2.u5357 (nat_lit 85929876) (nat_lit 7967630883) (nat_lit 0) A10K2.u5358 from rfl, allE_node, arows5357, irow5359, arows5358]
  all_goals rfl

theorem atot5359 : totK PA10K2 A10K2.u5359 = [0, 0, 1148055260332, 5354768765413, 8307257050340, 4565339579399, 713860433531, 19826178347, 0, 0] := by
  rw [show A10K2.u5359 = KTree.node A10K2.u5357 (nat_lit 85929876) (nat_lit 7967630883) (nat_lit 0) A10K2.u5358 from rfl, totK_node, atot5357, atot5358]
  decide +kernel

theorem arows5363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5363 = true := by
  rw [show A10K2.u5363 = KTree.node A10K2.u5361 (nat_lit 85949909) (nat_lit 3505417292) (nat_lit 0) A10K2.u5362 from rfl, allE_node, arows5361, irow5363, arows5362]
  all_goals rfl

theorem atot5363 : totK PA10K2 A10K2.u5363 = [0, 872304469579, 3386234346027, 5181203789168, 5450957813654, 3953078926910, 1012250332489, 62833682686, 0, 0] := by
  rw [show A10K2.u5363 = KTree.node A10K2.u5361 (nat_lit 85949909) (nat_lit 3505417292) (nat_lit 0) A10K2.u5362 from rfl, totK_node, atot5361, atot5362]
  decide +kernel

theorem arows5366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5366 = true := by
  rw [show A10K2.u5366 = KTree.node A10K2.u5364 (nat_lit 88687792) (nat_lit 6221595698) (nat_lit 0) A10K2.u5365 from rfl, allE_node, arows5364, irow5366, arows5365]
  all_goals rfl

theorem atot5366 : totK PA10K2 A10K2.u5366 = [0, 728110620904, 4356815309185, 8084366755777, 4952645036584, 823107497532, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5366 = KTree.node A10K2.u5364 (nat_lit 88687792) (nat_lit 6221595698) (nat_lit 0) A10K2.u5365 from rfl, totK_node, atot5364, atot5365]
  decide +kernel

theorem arows5375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5375 = true := by
  rw [show A10K2.u5375 = KTree.node A10K2.u5373 (nat_lit 88700114) (nat_lit 15653405069) (nat_lit 0) A10K2.u5374 from rfl, allE_node, arows5373, irow5375, arows5374]
  all_goals rfl

theorem atot5375 : totK PA10K2 A10K2.u5375 = [0, 743410903023, 4022547254100, 7625719534874, 5781121577335, 1479555745495, 81267323644, 0, 0, 0] := by
  rw [show A10K2.u5375 = KTree.node A10K2.u5373 (nat_lit 88700114) (nat_lit 15653405069) (nat_lit 0) A10K2.u5374 from rfl, totK_node, atot5373, atot5374]
  decide +kernel

theorem arows5378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5378 = true := by
  rw [show A10K2.u5378 = KTree.node A10K2.u5376 (nat_lit 88718342) (nat_lit 14594208750) (nat_lit 0) A10K2.u5377 from rfl, allE_node, arows5376, irow5378, arows5377]
  all_goals rfl

theorem atot5378 : totK PA10K2 A10K2.u5378 = [0, 0, 1052743488892, 5259164714266, 7971711350531, 3986889711673, 643031228427, 31082886609, 0, 0] := by
  rw [show A10K2.u5378 = KTree.node A10K2.u5376 (nat_lit 88718342) (nat_lit 14594208750) (nat_lit 0) A10K2.u5377 from rfl, totK_node, atot5376, atot5377]
  decide +kernel

theorem arows5382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5382 = true := by
  rw [show A10K2.u5382 = KTree.node A10K2.u5380 (nat_lit 88731208) (nat_lit 10073081492) (nat_lit 0) A10K2.u5381 from rfl, allE_node, arows5380, irow5382, arows5381]
  all_goals rfl

theorem atot5382 : totK PA10K2 A10K2.u5382 = [0, 468537272203, 2899081135625, 6498471118899, 6362237492684, 2503752924489, 280083003277, 6121173289, 0, 0] := by
  rw [show A10K2.u5382 = KTree.node A10K2.u5380 (nat_lit 88731208) (nat_lit 10073081492) (nat_lit 0) A10K2.u5381 from rfl, totK_node, atot5380, atot5381]
  decide +kernel

theorem arows5385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5385 = true := by
  rw [show A10K2.u5385 = KTree.node A10K2.u5383 (nat_lit 88749498) (nat_lit 14719078453) (nat_lit 0) A10K2.u5384 from rfl, allE_node, arows5383, irow5385, arows5384]
  all_goals rfl

theorem atot5385 : totK PA10K2 A10K2.u5385 = [0, 1291584452187, 5365705492629, 7592867564379, 4277515048678, 801294655385, 37229241746, 0, 0, 0] := by
  rw [show A10K2.u5385 = KTree.node A10K2.u5383 (nat_lit 88749498) (nat_lit 14719078453) (nat_lit 0) A10K2.u5384 from rfl, totK_node, atot5383, atot5384]
  decide +kernel

theorem arows5390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5390 = true := by
  rw [show A10K2.u5390 = KTree.node A10K2.u5388 (nat_lit 88768853) (nat_lit 6723517907) (nat_lit 0) A10K2.u5389 from rfl, allE_node, arows5388, irow5390, arows5389]
  all_goals rfl

theorem atot5390 : totK PA10K2 A10K2.u5390 = [0, 298263154340, 3172749091347, 7846537832671, 6182643560937, 1380744764447, 70813303540, 0, 0, 0] := by
  rw [show A10K2.u5390 = KTree.node A10K2.u5388 (nat_lit 88768853) (nat_lit 6723517907) (nat_lit 0) A10K2.u5389 from rfl, totK_node, atot5388, atot5389]
  decide +kernel

theorem arows5393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5393 = true := by
  rw [show A10K2.u5393 = KTree.node A10K2.u5391 (nat_lit 88789105) (nat_lit 7007920791) (nat_lit 0) A10K2.u5392 from rfl, allE_node, arows5391, irow5393, arows5392]
  all_goals rfl

theorem atot5393 : totK PA10K2 A10K2.u5393 = [0, 448034258811, 2587979028801, 6328904436036, 6894813001922, 2577815510964, 322913992912, 6354482628, 0, 0] := by
  rw [show A10K2.u5393 = KTree.node A10K2.u5391 (nat_lit 88789105) (nat_lit 7007920791) (nat_lit 0) A10K2.u5392 from rfl, totK_node, atot5391, atot5392]
  decide +kernel

theorem arows5397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5397 = true := by
  rw [show A10K2.u5397 = KTree.node A10K2.u5395 (nat_lit 88815392) (nat_lit 7364456456) (nat_lit 0) A10K2.u5396 from rfl, allE_node, arows5395, irow5397, arows5396]
  all_goals rfl

theorem atot5397 : totK PA10K2 A10K2.u5397 = [0, 1398226093687, 5784338353818, 7980480248708, 4068907379153, 692044077464, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u5397 = KTree.node A10K2.u5395 (nat_lit 88815392) (nat_lit 7364456456) (nat_lit 0) A10K2.u5396 from rfl, totK_node, atot5395, atot5396]
  decide +kernel

theorem arows5400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5400 = true := by
  rw [show A10K2.u5400 = KTree.node A10K2.u5398 (nat_lit 88834040) (nat_lit 12610577433) (nat_lit 0) A10K2.u5399 from rfl, allE_node, arows5398, irow5400, arows5399]
  all_goals rfl

theorem atot5400 : totK PA10K2 A10K2.u5400 = [0, 46039240014, 2214658547362, 7345136904375, 7693090014361, 2580606389520, 197745225792, 0, 0, 0] := by
  rw [show A10K2.u5400 = KTree.node A10K2.u5398 (nat_lit 88834040) (nat_lit 12610577433) (nat_lit 0) A10K2.u5399 from rfl, totK_node, atot5398, atot5399]
  decide +kernel

theorem arows5406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5406 = true := by
  rw [show A10K2.u5406 = KTree.node A10K2.u5404 (nat_lit 88859813) (nat_lit 5830587313) (nat_lit 0) A10K2.u5405 from rfl, allE_node, arows5404, irow5406, arows5405]
  all_goals rfl

theorem atot5406 : totK PA10K2 A10K2.u5406 = [0, 0, 1026122667074, 5138829968162, 8470877825100, 4834827642224, 650430458992, 13204174009, 0, 0] := by
  rw [show A10K2.u5406 = KTree.node A10K2.u5404 (nat_lit 88859813) (nat_lit 5830587313) (nat_lit 0) A10K2.u5405 from rfl, totK_node, atot5404, atot5405]
  decide +kernel

theorem arows5409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5409 = true := by
  rw [show A10K2.u5409 = KTree.node A10K2.u5407 (nat_lit 88943834) (nat_lit 14066612926) (nat_lit 0) A10K2.u5408 from rfl, allE_node, arows5407, irow5409, arows5408]
  all_goals rfl

theorem atot5409 : totK PA10K2 A10K2.u5409 = [0, 0, 957704055922, 4535993307287, 7583553423957, 5061529394254, 1159132813280, 67532844760, 0, 0] := by
  rw [show A10K2.u5409 = KTree.node A10K2.u5407 (nat_lit 88943834) (nat_lit 14066612926) (nat_lit 0) A10K2.u5408 from rfl, totK_node, atot5407, atot5408]
  decide +kernel

theorem arows5413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5413 = true := by
  rw [show A10K2.u5413 = KTree.node A10K2.u5411 (nat_lit 88955066) (nat_lit 14088912522) (nat_lit 0) A10K2.u5412 from rfl, allE_node, arows5411, irow5413, arows5412]
  all_goals rfl

theorem atot5413 : totK PA10K2 A10K2.u5413 = [0, 0, 1382040637232, 6054036381743, 8108648092377, 3296834281689, 321524215179, 6239673734, 0, 0] := by
  rw [show A10K2.u5413 = KTree.node A10K2.u5411 (nat_lit 88955066) (nat_lit 14088912522) (nat_lit 0) A10K2.u5412 from rfl, totK_node, atot5411, atot5412]
  decide +kernel

theorem arows5416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5416 = true := by
  rw [show A10K2.u5416 = KTree.node A10K2.u5414 (nat_lit 88975539) (nat_lit 10340491461) (nat_lit 0) A10K2.u5415 from rfl, allE_node, arows5414, irow5416, arows5415]
  all_goals rfl

theorem atot5416 : totK PA10K2 A10K2.u5416 = [0, 0, 0, 1457901812536, 6094823396702, 7750037819410, 3396403007515, 531894136737, 25565504801, 0] := by
  rw [show A10K2.u5416 = KTree.node A10K2.u5414 (nat_lit 88975539) (nat_lit 10340491461) (nat_lit 0) A10K2.u5415 from rfl, totK_node, atot5414, atot5415]
  decide +kernel

theorem arows5421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5421 = true := by
  rw [show A10K2.u5421 = KTree.node A10K2.u5419 (nat_lit 88986901) (nat_lit 6954779694) (nat_lit 0) A10K2.u5420 from rfl, allE_node, arows5419, irow5421, arows5420]
  all_goals rfl

theorem atot5421 : totK PA10K2 A10K2.u5421 = [0, 0, 103649551945, 1669462516071, 6188518401597, 7696073046064, 2977134713895, 374457576175, 11138589073, 0] := by
  rw [show A10K2.u5421 = KTree.node A10K2.u5419 (nat_lit 88986901) (nat_lit 6954779694) (nat_lit 0) A10K2.u5420 from rfl, totK_node, atot5419, atot5420]
  decide +kernel

theorem arows5424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5424 = true := by
  rw [show A10K2.u5424 = KTree.node A10K2.u5422 (nat_lit 89007853) (nat_lit 5399166982) (nat_lit 0) A10K2.u5423 from rfl, allE_node, arows5422, irow5424, arows5423]
  all_goals rfl

theorem atot5424 : totK PA10K2 A10K2.u5424 = [0, 0, 1164764774900, 5426163197500, 7947018301098, 3972509587412, 646343938345, 31195026185, 0, 0] := by
  rw [show A10K2.u5424 = KTree.node A10K2.u5422 (nat_lit 89007853) (nat_lit 5399166982) (nat_lit 0) A10K2.u5423 from rfl, totK_node, atot5422, atot5423]
  decide +kernel

theorem arows5428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5428 = true := by
  rw [show A10K2.u5428 = KTree.node A10K2.u5426 (nat_lit 89017010) (nat_lit 13689995678) (nat_lit 0) A10K2.u5427 from rfl, allE_node, arows5426, irow5428, arows5427]
  all_goals rfl

theorem atot5428 : totK PA10K2 A10K2.u5428 = [0, 0, 789970551885, 4474575311208, 8012407594381, 4725211983944, 722419780709, 18511492484, 0, 0] := by
  rw [show A10K2.u5428 = KTree.node A10K2.u5426 (nat_lit 89017010) (nat_lit 13689995678) (nat_lit 0) A10K2.u5427 from rfl, totK_node, atot5426, atot5427]
  decide +kernel

theorem arows5431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5431 = true := by
  rw [show A10K2.u5431 = KTree.node A10K2.u5429 (nat_lit 89048349) (nat_lit 6380033947) (nat_lit 0) A10K2.u5430 from rfl, allE_node, arows5429, irow5431, arows5430]
  all_goals rfl

theorem atot5431 : totK PA10K2 A10K2.u5431 = [0, 0, 120678695417, 1733914928938, 6427713205848, 7732411750363, 2623411662858, 267339084731, 6239673734, 0] := by
  rw [show A10K2.u5431 = KTree.node A10K2.u5429 (nat_lit 89048349) (nat_lit 6380033947) (nat_lit 0) A10K2.u5430 from rfl, totK_node, atot5429, atot5430]
  decide +kernel

theorem arows5438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5438 = true := by
  rw [show A10K2.u5438 = KTree.node A10K2.u5436 (nat_lit 89075072) (nat_lit 13777165684) (nat_lit 0) A10K2.u5437 from rfl, allE_node, arows5436, irow5438, arows5437]
  all_goals rfl

theorem atot5438 : totK PA10K2 A10K2.u5438 = [0, 0, 1161100967955, 5386181258726, 8179282239970, 4512305729032, 732295115107, 31285368086, 0, 0] := by
  rw [show A10K2.u5438 = KTree.node A10K2.u5436 (nat_lit 89075072) (nat_lit 13777165684) (nat_lit 0) A10K2.u5437 from rfl, totK_node, atot5436, atot5437]
  decide +kernel

theorem arows5441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5441 = true := by
  rw [show A10K2.u5441 = KTree.node A10K2.u5439 (nat_lit 89093631) (nat_lit 13977239216) (nat_lit 0) A10K2.u5440 from rfl, allE_node, arows5439, irow5441, arows5440]
  all_goals rfl

theorem atot5441 : totK PA10K2 A10K2.u5441 = [0, 597780859188, 2697908584267, 5307247827947, 6366916349591, 4053476089102, 888329764557, 42874818239, 0, 0] := by
  rw [show A10K2.u5441 = KTree.node A10K2.u5439 (nat_lit 89093631) (nat_lit 13977239216) (nat_lit 0) A10K2.u5440 from rfl, totK_node, atot5439, atot5440]
  decide +kernel

theorem arows5445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5445 = true := by
  rw [show A10K2.u5445 = KTree.node A10K2.u5443 (nat_lit 89145920) (nat_lit 15073067218) (nat_lit 0) A10K2.u5444 from rfl, allE_node, arows5443, irow5445, arows5444]
  all_goals rfl

theorem atot5445 : totK PA10K2 A10K2.u5445 = [0, 925615260218, 5029841596541, 8294330196084, 4344479860364, 626429575872, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5445 = KTree.node A10K2.u5443 (nat_lit 89145920) (nat_lit 15073067218) (nat_lit 0) A10K2.u5444 from rfl, totK_node, atot5443, atot5444]
  decide +kernel

theorem arows5448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5448 = true := by
  rw [show A10K2.u5448 = KTree.node A10K2.u5446 (nat_lit 89166337) (nat_lit 10551639029) (nat_lit 0) A10K2.u5447 from rfl, allE_node, arows5446, irow5448, arows5447]
  all_goals rfl

theorem atot5448 : totK PA10K2 A10K2.u5448 = [0, 0, 1423817107869, 5987572204130, 7772795003714, 3325497517016, 515119904239, 30650496230, 0, 0] := by
  rw [show A10K2.u5448 = KTree.node A10K2.u5446 (nat_lit 89166337) (nat_lit 10551639029) (nat_lit 0) A10K2.u5447 from rfl, totK_node, atot5446, atot5447]
  decide +kernel

theorem arows5453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5453 = true := by
  rw [show A10K2.u5453 = KTree.node A10K2.u5451 (nat_lit 89204773) (nat_lit 7234689464) (nat_lit 0) A10K2.u5452 from rfl, allE_node, arows5451, irow5453, arows5452]
  all_goals rfl

theorem atot5453 : totK PA10K2 A10K2.u5453 = [0, 836243354860, 3753481252192, 6629782061378, 5642386197240, 1973726679658, 224817926123, 5546304973, 0, 0] := by
  rw [show A10K2.u5453 = KTree.node A10K2.u5451 (nat_lit 89204773) (nat_lit 7234689464) (nat_lit 0) A10K2.u5452 from rfl, totK_node, atot5451, atot5452]
  decide +kernel

theorem arows5456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5456 = true := by
  rw [show A10K2.u5456 = KTree.node A10K2.u5454 (nat_lit 89213792) (nat_lit 11225403227) (nat_lit 0) A10K2.u5455 from rfl, allE_node, arows5454, irow5456, arows5455]
  all_goals rfl

theorem atot5456 : totK PA10K2 A10K2.u5456 = [0, 1325492871192, 5639467537811, 7878826892156, 3874446907465, 546231738105, 12388698189, 0, 0, 0] := by
  rw [show A10K2.u5456 = KTree.node A10K2.u5454 (nat_lit 89213792) (nat_lit 11225403227) (nat_lit 0) A10K2.u5455 from rfl, totK_node, atot5454, atot5455]
  decide +kernel

theorem arows5460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5460 = true := by
  rw [show A10K2.u5460 = KTree.node A10K2.u5458 (nat_lit 89237538) (nat_lit 9239556487) (nat_lit 0) A10K2.u5459 from rfl, allE_node, arows5458, irow5460, arows5459]
  all_goals rfl

theorem atot5460 : totK PA10K2 A10K2.u5460 = [0, 0, 1604481555407, 6221394954715, 7683214780387, 3320654614062, 497262428572, 25565504801, 0, 0] := by
  rw [show A10K2.u5460 = KTree.node A10K2.u5458 (nat_lit 89237538) (nat_lit 9239556487) (nat_lit 0) A10K2.u5459 from rfl, totK_node, atot5458, atot5459]
  decide +kernel

theorem arows5463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5463 = true := by
  rw [show A10K2.u5463 = KTree.node A10K2.u5461 (nat_lit 89248006) (nat_lit 7175988322) (nat_lit 0) A10K2.u5462 from rfl, allE_node, arows5461, irow5463, arows5462]
  all_goals rfl

theorem atot5463 : totK PA10K2 A10K2.u5463 = [0, 0, 1322992483750, 5791713352261, 8007585852675, 3561787821852, 429864526106, 11638555097, 0, 0] := by
  rw [show A10K2.u5463 = KTree.node A10K2.u5461 (nat_lit 89248006) (nat_lit 7175988322) (nat_lit 0) A10K2.u5462 from rfl, totK_node, atot5461, atot5462]
  decide +kernel

theorem arows5469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5469 = true := by
  rw [show A10K2.u5469 = KTree.node A10K2.u5467 (nat_lit 89266232) (nat_lit 14401970788) (nat_lit 0) A10K2.u5468 from rfl, allE_node, arows5467, irow5469, arows5468]
  all_goals rfl

theorem atot5469 : totK PA10K2 A10K2.u5469 = [0, 1416960118289, 5726383976276, 7549565377787, 3681180893003, 766133882346, 61027613725, 0, 0, 0] := by
  rw [show A10K2.u5469 = KTree.node A10K2.u5467 (nat_lit 89266232) (nat_lit 14401970788) (nat_lit 0) A10K2.u5468 from rfl, totK_node, atot5467, atot5468]
  decide +kernel

theorem arows5472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5472 = true := by
  rw [show A10K2.u5472 = KTree.node A10K2.u5470 (nat_lit 89277602) (nat_lit 14377112747) (nat_lit 0) A10K2.u5471 from rfl, allE_node, arows5470, irow5472, arows5471]
  all_goals rfl

theorem atot5472 : totK PA10K2 A10K2.u5472 = [0, 837613071177, 4715210153201, 8084842557533, 4638456341567, 768607336816, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5472 = KTree.node A10K2.u5470 (nat_lit 89277602) (nat_lit 14377112747) (nat_lit 0) A10K2.u5471 from rfl, totK_node, atot5470, atot5471]
  decide +kernel

theorem arows5476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5476 = true := by
  rw [show A10K2.u5476 = KTree.node A10K2.u5474 (nat_lit 89302771) (nat_lit 8433850578) (nat_lit 0) A10K2.u5475 from rfl, allE_node, arows5474, irow5476, arows5475]
  all_goals rfl

theorem atot5476 : totK PA10K2 A10K2.u5476 = [0, 0, 1940380510645, 7270318538240, 7645168032264, 2082298968529, 128845499320, 0, 0, 0] := by
  rw [show A10K2.u5476 = KTree.node A10K2.u5474 (nat_lit 89302771) (nat_lit 8433850578) (nat_lit 0) A10K2.u5475 from rfl, totK_node, atot5474, atot5475]
  decide +kernel

theorem arows5479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5479 = true := by
  rw [show A10K2.u5479 = KTree.node A10K2.u5477 (nat_lit 89391466) (nat_lit 8326272087) (nat_lit 0) A10K2.u5478 from rfl, allE_node, arows5477, irow5479, arows5478]
  all_goals rfl

theorem atot5479 : totK PA10K2 A10K2.u5479 = [0, 0, 1065844776333, 5317968273866, 8104351362860, 3876539334260, 612139254922, 31725663621, 0, 0] := by
  rw [show A10K2.u5479 = KTree.node A10K2.u5477 (nat_lit 89391466) (nat_lit 8326272087) (nat_lit 0) A10K2.u5478 from rfl, totK_node, atot5477, atot5478]
  decide +kernel

theorem arows5484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5484 = true := by
  rw [show A10K2.u5484 = KTree.node A10K2.u5482 (nat_lit 89410325) (nat_lit 7032552694) (nat_lit 0) A10K2.u5483 from rfl, allE_node, arows5482, irow5484, arows5483]
  all_goals rfl

theorem atot5484 : totK PA10K2 A10K2.u5484 = [0, 0, 1313649197113, 5527871833921, 7905060900618, 3816331908173, 509995349344, 11801668502, 0, 0] := by
  rw [show A10K2.u5484 = KTree.node A10K2.u5482 (nat_lit 89410325) (nat_lit 7032552694) (nat_lit 0) A10K2.u5483 from rfl, totK_node, atot5482, atot5483]
  decide +kernel

theorem arows5487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5487 = true := by
  rw [show A10K2.u5487 = KTree.node A10K2.u5485 (nat_lit 89472114) (nat_lit 11584367419) (nat_lit 0) A10K2.u5486 from rfl, allE_node, arows5485, irow5487, arows5486]
  all_goals rfl

theorem atot5487 : totK PA10K2 A10K2.u5487 = [0, 0, 1069955236134, 5212830745723, 7928076602990, 4172777050574, 671506145829, 31452573850, 0, 0] := by
  rw [show A10K2.u5487 = KTree.node A10K2.u5485 (nat_lit 89472114) (nat_lit 11584367419) (nat_lit 0) A10K2.u5486 from rfl, totK_node, atot5485, atot5486]
  decide +kernel

theorem arows5491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5491 = true := by
  rw [show A10K2.u5491 = KTree.node A10K2.u5489 (nat_lit 89485274) (nat_lit 13282809488) (nat_lit 0) A10K2.u5490 from rfl, allE_node, arows5489, irow5491, arows5490]
  all_goals rfl

theorem atot5491 : totK PA10K2 A10K2.u5491 = [0, 0, 1205883407080, 5383654614278, 8037099926569, 4230965639343, 597486787050, 13317224979, 0, 0] := by
  rw [show A10K2.u5491 = KTree.node A10K2.u5489 (nat_lit 89485274) (nat_lit 13282809488) (nat_lit 0) A10K2.u5490 from rfl, totK_node, atot5489, atot5490]
  decide +kernel

theorem arows5494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5494 = true := by
  rw [show A10K2.u5494 = KTree.node A10K2.u5492 (nat_lit 89532578) (nat_lit 14142712800) (nat_lit 0) A10K2.u5493 from rfl, allE_node, arows5492, irow5494, arows5493]
  all_goals rfl

theorem atot5494 : totK PA10K2 A10K2.u5494 = [0, 0, 764881778263, 4304331029856, 7861274750054, 4950628614028, 960668895767, 61078328232, 0, 0] := by
  rw [show A10K2.u5494 = KTree.node A10K2.u5492 (nat_lit 89532578) (nat_lit 14142712800) (nat_lit 0) A10K2.u5493 from rfl, totK_node, atot5492, atot5493]
  decide +kernel

theorem arows5502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5502 = true := by
  rw [show A10K2.u5502 = KTree.node A10K2.u5500 (nat_lit 89543049) (nat_lit 9596616231) (nat_lit 0) A10K2.u5501 from rfl, allE_node, arows5500, irow5502, arows5501]
  all_goals rfl

theorem atot5502 : totK PA10K2 A10K2.u5502 = [0, 0, 836002267270, 4506927492405, 7863395681973, 4646243850760, 833129916660, 37547833973, 0, 0] := by
  rw [show A10K2.u5502 = KTree.node A10K2.u5500 (nat_lit 89543049) (nat_lit 9596616231) (nat_lit 0) A10K2.u5501 from rfl, totK_node, atot5500, atot5501]
  decide +kernel

theorem arows5505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5505 = true := by
  rw [show A10K2.u5505 = KTree.node A10K2.u5503 (nat_lit 89572578) (nat_lit 14238202023) (nat_lit 0) A10K2.u5504 from rfl, allE_node, arows5503, irow5505, arows5504]
  all_goals rfl

theorem atot5505 : totK PA10K2 A10K2.u5505 = [0, 0, 0, 1623770011139, 6462939335808, 7498923123457, 2617918917572, 255874176371, 0, 0] := by
  rw [show A10K2.u5505 = KTree.node A10K2.u5503 (nat_lit 89572578) (nat_lit 14238202023) (nat_lit 0) A10K2.u5504 from rfl, totK_node, atot5503, atot5504]
  decide +kernel

theorem arows5509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5509 = true := by
  rw [show A10K2.u5509 = KTree.node A10K2.u5507 (nat_lit 89732452) (nat_lit 13494132798) (nat_lit 0) A10K2.u5508 from rfl, allE_node, arows5507, irow5509, arows5508]
  all_goals rfl

theorem atot5509 : totK PA10K2 A10K2.u5509 = [0, 1344953025193, 5497222905949, 7671958849346, 4045708516241, 692308086740, 150391853697, 91540553519, 6354482628, 0] := by
  rw [show A10K2.u5509 = KTree.node A10K2.u5507 (nat_lit 89732452) (nat_lit 13494132798) (nat_lit 0) A10K2.u5508 from rfl, totK_node, atot5507, atot5508]
  decide +kernel

theorem arows5512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5512 = true := by
  rw [show A10K2.u5512 = KTree.node A10K2.u5510 (nat_lit 89745306) (nat_lit 14875845437) (nat_lit 0) A10K2.u5511 from rfl, allE_node, arows5510, irow5512, arows5511]
  all_goals rfl

theorem atot5512 : totK PA10K2 A10K2.u5512 = [0, 866074750398, 4805234194632, 8443133293539, 5065766926540, 809175222873, 20168929705, 0, 0, 0] := by
  rw [show A10K2.u5512 = KTree.node A10K2.u5510 (nat_lit 89745306) (nat_lit 14875845437) (nat_lit 0) A10K2.u5511 from rfl, totK_node, atot5510, atot5511]
  decide +kernel

theorem arows5517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5517 = true := by
  rw [show A10K2.u5517 = KTree.node A10K2.u5515 (nat_lit 89763839) (nat_lit 12669053876) (nat_lit 0) A10K2.u5516 from rfl, allE_node, arows5515, irow5517, arows5516]
  all_goals rfl

theorem atot5517 : totK PA10K2 A10K2.u5517 = [0, 0, 1198069104360, 5368671336628, 7889178692360, 4112751220692, 679678830880, 31082886609, 0, 0] := by
  rw [show A10K2.u5517 = KTree.node A10K2.u5515 (nat_lit 89763839) (nat_lit 12669053876) (nat_lit 0) A10K2.u5516 from rfl, totK_node, atot5515, atot5516]
  decide +kernel

theorem arows5520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5520 = true := by
  rw [show A10K2.u5520 = KTree.node A10K2.u5518 (nat_lit 89777891) (nat_lit 10249410937) (nat_lit 0) A10K2.u5519 from rfl, allE_node, arows5518, irow5520, arows5519]
  all_goals rfl

theorem atot5520 : totK PA10K2 A10K2.u5520 = [0, 593238721492, 3171806833065, 6676527214587, 6583362948236, 2541719787589, 279327491423, 6121173289, 0, 0] := by
  rw [show A10K2.u5520 = KTree.node A10K2.u5518 (nat_lit 89777891) (nat_lit 10249410937) (nat_lit 0) A10K2.u5519 from rfl, totK_node, atot5518, atot5519]
  decide +kernel

theorem arows5524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5524 = true := by
  rw [show A10K2.u5524 = KTree.node A10K2.u5522 (nat_lit 89861297) (nat_lit 6174112270) (nat_lit 0) A10K2.u5523 from rfl, allE_node, arows5522, irow5524, arows5523]
  all_goals rfl

theorem atot5524 : totK PA10K2 A10K2.u5524 = [0, 993994451986, 4729208529247, 7923993118894, 5095261930718, 1008162917842, 45038009423, 0, 0, 0] := by
  rw [show A10K2.u5524 = KTree.node A10K2.u5522 (nat_lit 89861297) (nat_lit 6174112270) (nat_lit 0) A10K2.u5523 from rfl, totK_node, atot5522, atot5523]
  decide +kernel

theorem arows5527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5527 = true := by
  rw [show A10K2.u5527 = KTree.node A10K2.u5525 (nat_lit 89879303) (nat_lit 8479983140) (nat_lit 0) A10K2.u5526 from rfl, allE_node, arows5525, irow5527, arows5526]
  all_goals rfl

theorem atot5527 : totK PA10K2 A10K2.u5527 = [0, 658243994560, 4038416123776, 8007012849663, 5898246275246, 1425786333659, 76375693633, 0, 0, 0] := by
  rw [show A10K2.u5527 = KTree.node A10K2.u5525 (nat_lit 89879303) (nat_lit 8479983140) (nat_lit 0) A10K2.u5526 from rfl, totK_node, atot5525, atot5526]
  decide +kernel

theorem arows5533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5533 = true := by
  rw [show A10K2.u5533 = KTree.node A10K2.u5531 (nat_lit 89893077) (nat_lit 6184192715) (nat_lit 0) A10K2.u5532 from rfl, allE_node, arows5531, irow5533, arows5532]
  all_goals rfl

theorem atot5533 : totK PA10K2 A10K2.u5533 = [0, 0, 1007310387353, 5099475787099, 8412971061386, 4712686417212, 647641709227, 13951953716, 0, 0] := by
  rw [show A10K2.u5533 = KTree.node A10K2.u5531 (nat_lit 89893077) (nat_lit 6184192715) (nat_lit 0) A10K2.u5532 from rfl, totK_node, atot5531, atot5532]
  decide +kernel

theorem arows5536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5536 = true := by
  rw [show A10K2.u5536 = KTree.node A10K2.u5534 (nat_lit 89911814) (nat_lit 14956523810) (nat_lit 0) A10K2.u5535 from rfl, allE_node, arows5534, irow5536, arows5535]
  all_goals rfl

theorem atot5536 : totK PA10K2 A10K2.u5536 = [0, 0, 1078339319855, 5025246094849, 7829455804383, 4776232058557, 1019275706608, 61110126106, 0, 0] := by
  rw [show A10K2.u5536 = KTree.node A10K2.u5534 (nat_lit 89911814) (nat_lit 14956523810) (nat_lit 0) A10K2.u5535 from rfl, totK_node, atot5534, atot5535]
  decide +kernel

theorem arows5540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5540 = true := by
  rw [show A10K2.u5540 = KTree.node A10K2.u5538 (nat_lit 89995923) (nat_lit 10899815526) (nat_lit 0) A10K2.u5539 from rfl, allE_node, arows5538, irow5540, arows5539]
  all_goals rfl

theorem atot5540 : totK PA10K2 A10K2.u5540 = [0, 0, 1090363326388, 5274595494524, 8055645695003, 4254799217841, 686456099361, 31306924438, 0, 0] := by
  rw [show A10K2.u5540 = KTree.node A10K2.u5538 (nat_lit 89995923) (nat_lit 10899815526) (nat_lit 0) A10K2.u5539 from rfl, totK_node, atot5538, atot5539]
  decide +kernel

theorem arows5543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5543 = true := by
  rw [show A10K2.u5543 = KTree.node A10K2.u5541 (nat_lit 90009609) (nat_lit 9766677555) (nat_lit 0) A10K2.u5542 from rfl, allE_node, arows5541, irow5543, arows5542]
  all_goals rfl

theorem atot5543 : totK PA10K2 A10K2.u5543 = [0, 0, 804002626082, 4175645972802, 7924530019710, 5819789021869, 1311848816806, 69661130078, 0, 0] := by
  rw [show A10K2.u5543 = KTree.node A10K2.u5541 (nat_lit 90009609) (nat_lit 9766677555) (nat_lit 0) A10K2.u5542 from rfl, totK_node, atot5541, atot5542]
  decide +kernel

theorem arows5548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5548 = true := by
  rw [show A10K2.u5548 = KTree.node A10K2.u5546 (nat_lit 90029452) (nat_lit 857097809) (nat_lit 0) A10K2.u5547 from rfl, allE_node, arows5546, irow5548, arows5547]
  all_goals rfl

theorem atot5548 : totK PA10K2 A10K2.u5548 = [0, 0, 0, 1883333678812, 6956643856493, 7702997294069, 2809276227511, 326161542922, 7151180950, 0] := by
  rw [show A10K2.u5548 = KTree.node A10K2.u5546 (nat_lit 90029452) (nat_lit 857097809) (nat_lit 0) A10K2.u5547 from rfl, totK_node, atot5546, atot5547]
  decide +kernel

theorem arows5551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5551 = true := by
  rw [show A10K2.u5551 = KTree.node A10K2.u5549 (nat_lit 90119269) (nat_lit 3032714410) (nat_lit 32) A10K2.u5550 from rfl, allE_node, arows5549, irow5551, arows5550]
  all_goals rfl

theorem atot5551 : totK PA10K2 A10K2.u5551 = [0, 0, 1376633234433, 5829993265804, 8036308107043, 4102496580032, 747556767838, 40355690693, 0, 0] := by
  rw [show A10K2.u5551 = KTree.node A10K2.u5549 (nat_lit 90119269) (nat_lit 3032714410) (nat_lit 32) A10K2.u5550 from rfl, totK_node, atot5549, atot5550]
  decide +kernel

theorem arows5555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5555 = true := by
  rw [show A10K2.u5555 = KTree.node A10K2.u5553 (nat_lit 90138454) (nat_lit 11485870967) (nat_lit 0) A10K2.u5554 from rfl, allE_node, arows5553, irow5555, arows5554]
  all_goals rfl

theorem atot5555 : totK PA10K2 A10K2.u5555 = [0, 0, 867349456065, 4539984135992, 8156327649236, 5434818086298, 935653803806, 25872399942, 0, 0] := by
  rw [show A10K2.u5555 = KTree.node A10K2.u5553 (nat_lit 90138454) (nat_lit 11485870967) (nat_lit 0) A10K2.u5554 from rfl, totK_node, atot5553, atot5554]
  decide +kernel

theorem arows5558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5558 = true := by
  rw [show A10K2.u5558 = KTree.node A10K2.u5556 (nat_lit 92278350) (nat_lit 10893499012) (nat_lit 0) A10K2.u5557 from rfl, allE_node, arows5556, irow5558, arows5557]
  all_goals rfl

theorem atot5558 : totK PA10K2 A10K2.u5558 = [0, 1137674346764, 4810017437868, 6852322833112, 4187068624969, 1698047322724, 540215223701, 49180423016, 0, 0] := by
  rw [show A10K2.u5558 = KTree.node A10K2.u5556 (nat_lit 92278350) (nat_lit 10893499012) (nat_lit 0) A10K2.u5557 from rfl, totK_node, atot5556, atot5557]
  decide +kernel

theorem arows5565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5565 = true := by
  rw [show A10K2.u5565 = KTree.node A10K2.u5563 (nat_lit 92297761) (nat_lit 9752342652) (nat_lit 0) A10K2.u5564 from rfl, allE_node, arows5563, irow5565, arows5564]
  all_goals rfl

theorem atot5565 : totK PA10K2 A10K2.u5565 = [0, 1080968927244, 5178039206126, 8070107737633, 4315807282711, 627185410715, 13207830636, 0, 0, 0] := by
  rw [show A10K2.u5565 = KTree.node A10K2.u5563 (nat_lit 92297761) (nat_lit 9752342652) (nat_lit 0) A10K2.u5564 from rfl, totK_node, atot5563, atot5564]
  decide +kernel

theorem arows5568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5568 = true := by
  rw [show A10K2.u5568 = KTree.node A10K2.u5566 (nat_lit 92310940) (nat_lit 1222845814) (nat_lit 0) A10K2.u5567 from rfl, allE_node, arows5566, irow5568, arows5567]
  all_goals rfl

theorem atot5568 : totK PA10K2 A10K2.u5568 = [0, 0, 1449667860384, 5812431342303, 7585617992060, 3639498053409, 616810498435, 30650496230, 0, 0] := by
  rw [show A10K2.u5568 = KTree.node A10K2.u5566 (nat_lit 92310940) (nat_lit 1222845814) (nat_lit 0) A10K2.u5567 from rfl, totK_node, atot5566, atot5567]
  decide +kernel

theorem arows5572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5572 = true := by
  rw [show A10K2.u5572 = KTree.node A10K2.u5570 (nat_lit 92330551) (nat_lit 5668502619) (nat_lit 0) A10K2.u5571 from rfl, allE_node, arows5570, irow5572, arows5571]
  all_goals rfl

theorem atot5572 : totK PA10K2 A10K2.u5572 = [0, 345421315675, 2232212663844, 6195650862791, 7319805710573, 2838744235466, 287725756872, 5546304973, 0, 0] := by
  rw [show A10K2.u5572 = KTree.node A10K2.u5570 (nat_lit 92330551) (nat_lit 5668502619) (nat_lit 0) A10K2.u5571 from rfl, totK_node, atot5570, atot5571]
  decide +kernel

theorem arows5575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5575 = true := by
  rw [show A10K2.u5575 = KTree.node A10K2.u5573 (nat_lit 92412707) (nat_lit 9106695611) (nat_lit 0) A10K2.u5574 from rfl, allE_node, arows5573, irow5575, arows5574]
  all_goals rfl

theorem atot5575 : totK PA10K2 A10K2.u5575 = [0, 991801321637, 4832170283610, 7717858954792, 4590342742728, 938282040730, 56566207178, 0, 0, 0] := by
  rw [show A10K2.u5575 = KTree.node A10K2.u5573 (nat_lit 92412707) (nat_lit 9106695611) (nat_lit 0) A10K2.u5574 from rfl, totK_node, atot5573, atot5574]
  decide +kernel

theorem arows5580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5580 = true := by
  rw [show A10K2.u5580 = KTree.node A10K2.u5578 (nat_lit 92424894) (nat_lit 4472164676) (nat_lit 0) A10K2.u5579 from rfl, allE_node, arows5578, irow5580, arows5579]
  all_goals rfl

theorem atot5580 : totK PA10K2 A10K2.u5580 = [0, 820244515340, 4483939616651, 7869346028371, 4906452000226, 879309275100, 38021971230, 0, 0, 0] := by
  rw [show A10K2.u5580 = KTree.node A10K2.u5578 (nat_lit 92424894) (nat_lit 4472164676) (nat_lit 0) A10K2.u5579 from rfl, totK_node, atot5578, atot5579]
  decide +kernel

theorem arows5583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5583 = true := by
  rw [show A10K2.u5583 = KTree.node A10K2.u5581 (nat_lit 92455177) (nat_lit 9757796508) (nat_lit 0) A10K2.u5582 from rfl, allE_node, arows5581, irow5583, arows5582]
  all_goals rfl

theorem atot5583 : totK PA10K2 A10K2.u5583 = [0, 0, 1674383722672, 6849826937148, 7895706252129, 2341673105344, 154391796764, 0, 0, 0] := by
  rw [show A10K2.u5583 = KTree.node A10K2.u5581 (nat_lit 92455177) (nat_lit 9757796508) (nat_lit 0) A10K2.u5582 from rfl, totK_node, atot5581, atot5582]
  decide +kernel

theorem arows5587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5587 = true := by
  rw [show A10K2.u5587 = KTree.node A10K2.u5585 (nat_lit 92475277) (nat_lit 2821671888) (nat_lit 0) A10K2.u5586 from rfl, allE_node, arows5585, irow5587, arows5586]
  all_goals rfl

theorem atot5587 : totK PA10K2 A10K2.u5587 = [0, 1161485721818, 4833752603322, 7114141442273, 4643734521685, 1518408699689, 238080587205, 6354482628, 0, 0] := by
  rw [show A10K2.u5587 = KTree.node A10K2.u5585 (nat_lit 92475277) (nat_lit 2821671888) (nat_lit 0) A10K2.u5586 from rfl, totK_node, atot5585, atot5586]
  decide +kernel

theorem arows5590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5590 = true := by
  rw [show A10K2.u5590 = KTree.node A10K2.u5588 (nat_lit 92504978) (nat_lit 6539166350) (nat_lit 0) A10K2.u5589 from rfl, allE_node, arows5588, irow5590, arows5589]
  all_goals rfl

theorem atot5590 : totK PA10K2 A10K2.u5590 = [0, 202896141557, 2278891488857, 6734765670186, 7424966198822, 2910536015057, 328851735615, 6904928264, 0, 0] := by
  rw [show A10K2.u5590 = KTree.node A10K2.u5588 (nat_lit 92504978) (nat_lit 6539166350) (nat_lit 0) A10K2.u5589 from rfl, totK_node, atot5588, atot5589]
  decide +kernel

theorem arows5596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5596 = true := by
  rw [show A10K2.u5596 = KTree.node A10K2.u5594 (nat_lit 92536304) (nat_lit 13804357183) (nat_lit 0) A10K2.u5595 from rfl, allE_node, arows5594, irow5596, arows5595]
  all_goals rfl

theorem atot5596 : totK PA10K2 A10K2.u5596 = [0, 0, 1436115148553, 6079085082240, 8137583264683, 3591248163514, 386534193325, 6066958478, 0, 0] := by
  rw [show A10K2.u5596 = KTree.node A10K2.u5594 (nat_lit 92536304) (nat_lit 13804357183) (nat_lit 0) A10K2.u5595 from rfl, totK_node, atot5594, atot5595]
  decide +kernel

theorem arows5599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5599 = true := by
  rw [show A10K2.u5599 = KTree.node A10K2.u5597 (nat_lit 92555037) (nat_lit 6324453213) (nat_lit 0) A10K2.u5598 from rfl, allE_node, arows5597, irow5599, arows5598]
  all_goals rfl

theorem atot5599 : totK PA10K2 A10K2.u5599 = [0, 0, 1039433784226, 4902266126487, 7745664582431, 4299198081865, 746264363151, 36536693801, 0, 0] := by
  rw [show A10K2.u5599 = KTree.node A10K2.u5597 (nat_lit 92555037) (nat_lit 6324453213) (nat_lit 0) A10K2.u5598 from rfl, totK_node, atot5597, atot5598]
  decide +kernel

theorem arows5603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5603 = true := by
  rw [show A10K2.u5603 = KTree.node A10K2.u5601 (nat_lit 92569993) (nat_lit 9623824707) (nat_lit 0) A10K2.u5602 from rfl, allE_node, arows5601, irow5603, arows5602]
  all_goals rfl

theorem atot5603 : totK PA10K2 A10K2.u5603 = [0, 0, 332048780867, 2871229412398, 7241159500418, 6508003897781, 2177557665139, 338262430621, 25239774317, 0] := by
  rw [show A10K2.u5603 = KTree.node A10K2.u5601 (nat_lit 92569993) (nat_lit 9623824707) (nat_lit 0) A10K2.u5602 from rfl, totK_node, atot5601, atot5602]
  decide +kernel

theorem arows5606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5606 = true := by
  rw [show A10K2.u5606 = KTree.node A10K2.u5604 (nat_lit 92590134) (nat_lit 14636161012) (nat_lit 0) A10K2.u5605 from rfl, allE_node, arows5604, irow5606, arows5605]
  all_goals rfl

theorem atot5606 : totK PA10K2 A10K2.u5606 = [0, 0, 304573652302, 2114502487087, 5951697541152, 7044422217008, 2851818471257, 378189061579, 10894784572, 0] := by
  rw [show A10K2.u5606 = KTree.node A10K2.u5604 (nat_lit 92590134) (nat_lit 14636161012) (nat_lit 0) A10K2.u5605 from rfl, totK_node, atot5604, atot5605]
  decide +kernel

theorem arows5611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5611 = true := by
  rw [show A10K2.u5611 = KTree.node A10K2.u5609 (nat_lit 92674259) (nat_lit 9583593223) (nat_lit 0) A10K2.u5610 from rfl, allE_node, arows5609, irow5611, arows5610]
  all_goals rfl

theorem atot5611 : totK PA10K2 A10K2.u5611 = [0, 0, 1032221562138, 5222003963721, 8124626616002, 4052672425169, 603462982896, 30831673886, 0, 0] := by
  rw [show A10K2.u5611 = KTree.node A10K2.u5609 (nat_lit 92674259) (nat_lit 9583593223) (nat_lit 0) A10K2.u5610 from rfl, totK_node, atot5609, atot5610]
  decide +kernel

theorem arows5614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5614 = true := by
  rw [show A10K2.u5614 = KTree.node A10K2.u5612 (nat_lit 92687038) (nat_lit 4472164676) (nat_lit 0) A10K2.u5613 from rfl, allE_node, arows5612, irow5614, arows5613]
  all_goals rfl

theorem atot5614 : totK PA10K2 A10K2.u5614 = [0, 0, 819545818442, 4467630480636, 7886370097548, 4701226543068, 830128458744, 38021971230, 0, 0] := by
  rw [show A10K2.u5614 = KTree.node A10K2.u5612 (nat_lit 92687038) (nat_lit 4472164676) (nat_lit 0) A10K2.u5613 from rfl, totK_node, atot5612, atot5613]
  decide +kernel

theorem arows5618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5618 = true := by
  rw [show A10K2.u5618 = KTree.node A10K2.u5616 (nat_lit 92717893) (nat_lit 6380572133) (nat_lit 0) A10K2.u5617 from rfl, allE_node, arows5616, irow5618, arows5617]
  all_goals rfl

theorem atot5618 : totK PA10K2 A10K2.u5618 = [0, 0, 27745223503, 1683842495900, 6689350784465, 7496157405441, 2386589234484, 242085458233, 5676195732, 0] := by
  rw [show A10K2.u5618 = KTree.node A10K2.u5616 (nat_lit 92717893) (nat_lit 6380572133) (nat_lit 0) A10K2.u5617 from rfl, totK_node, atot5616, atot5617]
  decide +kernel

theorem arows5621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5621 = true := by
  rw [show A10K2.u5621 = KTree.node A10K2.u5619 (nat_lit 92738166) (nat_lit 13596205329) (nat_lit 0) A10K2.u5620 from rfl, allE_node, arows5619, irow5621, arows5620]
  all_goals rfl

theorem atot5621 : totK PA10K2 A10K2.u5621 = [0, 0, 1317635705331, 5919850709809, 8289226868988, 3788759577540, 471130391087, 20058242317, 0, 0] := by
  rw [show A10K2.u5621 = KTree.node A10K2.u5619 (nat_lit 92738166) (nat_lit 13596205329) (nat_lit 0) A10K2.u5620 from rfl, totK_node, atot5619, atot5620]
  decide +kernel

theorem arows5631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5631 = true := by
  rw [show A10K2.u5631 = KTree.node A10K2.u5629 (nat_lit 92876210) (nat_lit 14586405808) (nat_lit 0) A10K2.u5630 from rfl, allE_node, arows5629, irow5631, arows5630]
  all_goals rfl

theorem atot5631 : totK PA10K2 A10K2.u5631 = [0, 1017276452227, 4405585411074, 6839192370951, 5024815030778, 1888417874232, 280217629823, 6853348008, 0, 0] := by
  rw [show A10K2.u5631 = KTree.node A10K2.u5629 (nat_lit 92876210) (nat_lit 14586405808) (nat_lit 0) A10K2.u5630 from rfl, totK_node, atot5629, atot5630]
  decide +kernel

theorem arows5634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5634 = true := by
  rw [show A10K2.u5634 = KTree.node A10K2.u5632 (nat_lit 92887231) (nat_lit 5767331198) (nat_lit 0) A10K2.u5633 from rfl, allE_node, arows5632, irow5634, arows5633]
  all_goals rfl

theorem atot5634 : totK PA10K2 A10K2.u5634 = [0, 1207602960733, 5646361207485, 8282333872532, 3877186500023, 455500850894, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5634 = KTree.node A10K2.u5632 (nat_lit 92887231) (nat_lit 5767331198) (nat_lit 0) A10K2.u5633 from rfl, totK_node, atot5632, atot5633]
  decide +kernel

theorem arows5638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5638 = true := by
  rw [show A10K2.u5638 = KTree.node A10K2.u5636 (nat_lit 92908592) (nat_lit 6758312621) (nat_lit 0) A10K2.u5637 from rfl, allE_node, arows5636, irow5638, arows5637]
  all_goals rfl

theorem atot5638 : totK PA10K2 A10K2.u5638 = [0, 0, 1221741671093, 5498232335287, 7915867215429, 3949859564471, 643122105712, 31082886609, 0, 0] := by
  rw [show A10K2.u5638 = KTree.node A10K2.u5636 (nat_lit 92908592) (nat_lit 6758312621) (nat_lit 0) A10K2.u5637 from rfl, totK_node, atot5636, atot5637]
  decide +kernel

theorem arows5641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5641 = true := by
  rw [show A10K2.u5641 = KTree.node A10K2.u5639 (nat_lit 92919920) (nat_lit 7931050688) (nat_lit 0) A10K2.u5640 from rfl, allE_node, arows5639, irow5641, arows5640]
  all_goals rfl

theorem atot5641 : totK PA10K2 A10K2.u5641 = [0, 273815470041, 1996079395307, 5988295683115, 7522228383914, 3074793287502, 314197479167, 6121173289, 0, 0] := by
  rw [show A10K2.u5641 = KTree.node A10K2.u5639 (nat_lit 92919920) (nat_lit 7931050688) (nat_lit 0) A10K2.u5640 from rfl, totK_node, atot5639, atot5640]
  decide +kernel

theorem arows5646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5646 = true := by
  rw [show A10K2.u5646 = KTree.node A10K2.u5644 (nat_lit 92939520) (nat_lit 8424027269) (nat_lit 0) A10K2.u5645 from rfl, allE_node, arows5644, irow5646, arows5645]
  all_goals rfl

theorem atot5646 : totK PA10K2 A10K2.u5646 = [0, 1064527805056, 5036288141060, 7776775391753, 4410932908197, 859159188705, 51172584006, 0, 0, 0] := by
  rw [show A10K2.u5646 = KTree.node A10K2.u5644 (nat_lit 92939520) (nat_lit 8424027269) (nat_lit 0) A10K2.u5645 from rfl, totK_node, atot5644, atot5645]
  decide +kernel

theorem arows5649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5649 = true := by
  rw [show A10K2.u5649 = KTree.node A10K2.u5647 (nat_lit 92948626) (nat_lit 15235736758) (nat_lit 0) A10K2.u5648 from rfl, allE_node, arows5647, irow5649, arows5648]
  all_goals rfl

theorem atot5649 : totK PA10K2 A10K2.u5649 = [0, 820391935196, 4547194055883, 8024863194548, 4770509706572, 786645561401, 32757061980, 0, 0, 0] := by
  rw [show A10K2.u5649 = KTree.node A10K2.u5647 (nat_lit 92948626) (nat_lit 15235736758) (nat_lit 0) A10K2.u5648 from rfl, totK_node, atot5647, atot5648]
  decide +kernel

theorem arows5653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5653 = true := by
  rw [show A10K2.u5653 = KTree.node A10K2.u5651 (nat_lit 92974542) (nat_lit 10246417045) (nat_lit 0) A10K2.u5652 from rfl, allE_node, arows5651, irow5653, arows5652]
  all_goals rfl

theorem atot5653 : totK PA10K2 A10K2.u5653 = [0, 0, 1878638429647, 7148857417047, 7759268920320, 2124109809670, 132493302491, 0, 0, 0] := by
  rw [show A10K2.u5653 = KTree.node A10K2.u5651 (nat_lit 92974542) (nat_lit 10246417045) (nat_lit 0) A10K2.u5652 from rfl, totK_node, atot5651, atot5652]
  decide +kernel

theorem arows5656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5656 = true := by
  rw [show A10K2.u5656 = KTree.node A10K2.u5654 (nat_lit 93007059) (nat_lit 10776653335) (nat_lit 0) A10K2.u5655 from rfl, allE_node, arows5654, irow5656, arows5655]
  all_goals rfl

theorem atot5656 : totK PA10K2 A10K2.u5656 = [0, 1061690136320, 4299761367944, 6691673504153, 5325075822834, 1930068116576, 271651963214, 6354482628, 0, 0] := by
  rw [show A10K2.u5656 = KTree.node A10K2.u5654 (nat_lit 93007059) (nat_lit 10776653335) (nat_lit 0) A10K2.u5655 from rfl, totK_node, atot5654, atot5655]
  decide +kernel

theorem arows5662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5662 = true := by
  rw [show A10K2.u5662 = KTree.node A10K2.u5660 (nat_lit 93037928) (nat_lit 4926169205) (nat_lit 0) A10K2.u5661 from rfl, allE_node, arows5660, irow5662, arows5661]
  all_goals rfl

theorem atot5662 : totK PA10K2 A10K2.u5662 = [0, 307923820525, 2855370519410, 7333886549629, 6868728722019, 2458715921720, 292929485446, 7047025452, 0, 0] := by
  rw [show A10K2.u5662 = KTree.node A10K2.u5660 (nat_lit 93037928) (nat_lit 4926169205) (nat_lit 0) A10K2.u5661 from rfl, totK_node, atot5660, atot5661]
  decide +kernel

theorem arows5665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5665 = true := by
  rw [show A10K2.u5665 = KTree.node A10K2.u5663 (nat_lit 93058967) (nat_lit 14322617938) (nat_lit 0) A10K2.u5664 from rfl, allE_node, arows5663, irow5665, arows5664]
  all_goals rfl

theorem atot5665 : totK PA10K2 A10K2.u5665 = [0, 0, 1441066053211, 6090466780306, 8233438237593, 3675661197503, 383676213629, 6157148557, 0, 0] := by
  rw [show A10K2.u5665 = KTree.node A10K2.u5663 (nat_lit 93058967) (nat_lit 14322617938) (nat_lit 0) A10K2.u5664 from rfl, totK_node, atot5663, atot5664]
  decide +kernel

theorem arows5669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5669 = true := by
  rw [show A10K2.u5669 = KTree.node A10K2.u5667 (nat_lit 93144347) (nat_lit 10025055015) (nat_lit 0) A10K2.u5668 from rfl, allE_node, arows5667, irow5669, arows5668]
  all_goals rfl

theorem atot5669 : totK PA10K2 A10K2.u5669 = [0, 0, 747245429164, 4339745583115, 7993150032519, 4923737987780, 819738798675, 31768748853, 0, 0] := by
  rw [show A10K2.u5669 = KTree.node A10K2.u5667 (nat_lit 93144347) (nat_lit 10025055015) (nat_lit 0) A10K2.u5668 from rfl, totK_node, atot5667, atot5668]
  decide +kernel

theorem arows5672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5672 = true := by
  rw [show A10K2.u5672 = KTree.node A10K2.u5670 (nat_lit 93158640) (nat_lit 11133278244) (nat_lit 0) A10K2.u5671 from rfl, allE_node, arows5670, irow5672, arows5671]
  all_goals rfl

theorem atot5672 : totK PA10K2 A10K2.u5672 = [0, 0, 627544772511, 3771593251462, 7815913675142, 6096803874958, 1468146227783, 86677628435, 0, 0] := by
  rw [show A10K2.u5672 = KTree.node A10K2.u5670 (nat_lit 93158640) (nat_lit 11133278244) (nat_lit 0) A10K2.u5671 from rfl, totK_node, atot5670, atot5671]
  decide +kernel

theorem arows5677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5677 = true := by
  rw [show A10K2.u5677 = KTree.node A10K2.u5675 (nat_lit 93178078) (nat_lit 10468896591) (nat_lit 0) A10K2.u5676 from rfl, allE_node, arows5675, irow5677, arows5676]
  all_goals rfl

theorem atot5677 : totK PA10K2 A10K2.u5677 = [0, 0, 0, 1279983805350, 5445874150542, 7580154508249, 3709178241071, 651302111241, 36704093874, 0] := by
  rw [show A10K2.u5677 = KTree.node A10K2.u5675 (nat_lit 93178078) (nat_lit 10468896591) (nat_lit 0) A10K2.u5676 from rfl, totK_node, atot5675, atot5676]
  decide +kernel

theorem arows5680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5680 = true := by
  rw [show A10K2.u5680 = KTree.node A10K2.u5678 (nat_lit 93201558) (nat_lit 14612539823) (nat_lit 0) A10K2.u5679 from rfl, allE_node, arows5678, irow5680, arows5679]
  all_goals rfl

theorem atot5680 : totK PA10K2 A10K2.u5680 = [0, 0, 1337977996624, 5805767905372, 7990884860080, 3571214510057, 488610262485, 25801403013, 0, 0] := by
  rw [show A10K2.u5680 = KTree.node A10K2.u5678 (nat_lit 93201558) (nat_lit 14612539823) (nat_lit 0) A10K2.u5679 from rfl, totK_node, atot5678, atot5679]
  decide +kernel

theorem arows5684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5684 = true := by
  rw [show A10K2.u5684 = KTree.node A10K2.u5682 (nat_lit 93210679) (nat_lit 3948942480) (nat_lit 0) A10K2.u5683 from rfl, allE_node, arows5682, irow5684, arows5683]
  all_goals rfl

theorem atot5684 : totK PA10K2 A10K2.u5684 = [0, 0, 820027295343, 4536628090111, 8043122007648, 4664630479571, 709175040339, 17782321361, 0, 0] := by
  rw [show A10K2.u5684 = KTree.node A10K2.u5682 (nat_lit 93210679) (nat_lit 3948942480) (nat_lit 0) A10K2.u5683 from rfl, totK_node, atot5682, atot5683]
  decide +kernel

theorem arows5687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5687 = true := by
  rw [show A10K2.u5687 = KTree.node A10K2.u5685 (nat_lit 93236890) (nat_lit 15094184054) (nat_lit 0) A10K2.u5686 from rfl, allE_node, arows5685, irow5687, arows5686]
  all_goals rfl

theorem atot5687 : totK PA10K2 A10K2.u5687 = [0, 0, 0, 1873326351417, 7256776323903, 7668957227619, 1860274873432, 99706046597, 0, 0] := by
  rw [show A10K2.u5687 = KTree.node A10K2.u5685 (nat_lit 93236890) (nat_lit 15094184054) (nat_lit 0) A10K2.u5686 from rfl, totK_node, atot5685, atot5686]
  decide +kernel

theorem arows5694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5694 = true := by
  rw [show A10K2.u5694 = KTree.node A10K2.u5692 (nat_lit 93269559) (nat_lit 14876574687) (nat_lit 0) A10K2.u5693 from rfl, allE_node, arows5692, irow5694, arows5693]
  all_goals rfl

theorem atot5694 : totK PA10K2 A10K2.u5694 = [0, 0, 1139531954707, 4838458549429, 7121999098946, 4665025457094, 1538898683122, 222295685760, 6239673734, 0] := by
  rw [show A10K2.u5694 = KTree.node A10K2.u5692 (nat_lit 93269559) (nat_lit 14876574687) (nat_lit 0) A10K2.u5693 from rfl, totK_node, atot5692, atot5693]
  decide +kernel

theorem arows5697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5697 = true := by
  rw [show A10K2.u5697 = KTree.node A10K2.u5695 (nat_lit 93324169) (nat_lit 9410466366) (nat_lit 0) A10K2.u5696 from rfl, allE_node, arows5695, irow5697, arows5696]
  all_goals rfl

theorem atot5697 : totK PA10K2 A10K2.u5697 = [0, 800527158634, 3714474020089, 6512193224150, 5639083805163, 2493492376251, 348901538658, 6962742351, 0, 0] := by
  rw [show A10K2.u5697 = KTree.node A10K2.u5695 (nat_lit 93324169) (nat_lit 9410466366) (nat_lit 0) A10K2.u5696 from rfl, totK_node, atot5695, atot5696]
  decide +kernel

theorem arows5701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5701 = true := by
  rw [show A10K2.u5701 = KTree.node A10K2.u5699 (nat_lit 93342568) (nat_lit 9029519495) (nat_lit 0) A10K2.u5700 from rfl, allE_node, arows5699, irow5701, arows5700]
  all_goals rfl

theorem atot5701 : totK PA10K2 A10K2.u5701 = [0, 1244898366231, 5531862281286, 7954691521656, 3873407791107, 523557833923, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u5701 = KTree.node A10K2.u5699 (nat_lit 93342568) (nat_lit 9029519495) (nat_lit 0) A10K2.u5700 from rfl, totK_node, atot5699, atot5700]
  decide +kernel

theorem arows5704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5704 = true := by
  rw [show A10K2.u5704 = KTree.node A10K2.u5702 (nat_lit 93358890) (nat_lit 10039776918) (nat_lit 0) A10K2.u5703 from rfl, allE_node, arows5702, irow5704, arows5703]
  all_goals rfl

theorem atot5704 : totK PA10K2 A10K2.u5704 = [0, 0, 1428593285373, 5765091495250, 7608946492974, 3465505408471, 541603313505, 30650496230, 0, 0] := by
  rw [show A10K2.u5704 = KTree.node A10K2.u5702 (nat_lit 93358890) (nat_lit 10039776918) (nat_lit 0) A10K2.u5703 from rfl, totK_node, atot5702, atot5703]
  decide +kernel

theorem arows5709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5709 = true := by
  rw [show A10K2.u5709 = KTree.node A10K2.u5707 (nat_lit 93378786) (nat_lit 12095314195) (nat_lit 0) A10K2.u5708 from rfl, allE_node, arows5707, irow5709, arows5708]
  all_goals rfl

theorem atot5709 : totK PA10K2 A10K2.u5709 = [0, 449259150676, 2494259709690, 6269245553916, 7035734938420, 2613120371921, 263432337464, 5546304973, 0, 0] := by
  rw [show A10K2.u5709 = KTree.node A10K2.u5707 (nat_lit 93378786) (nat_lit 12095314195) (nat_lit 0) A10K2.u5708 from rfl, totK_node, atot5707, atot5708]
  decide +kernel

theorem arows5712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5712 = true := by
  rw [show A10K2.u5712 = KTree.node A10K2.u5710 (nat_lit 93403990) (nat_lit 8453425429) (nat_lit 0) A10K2.u5711 from rfl, allE_node, arows5710, irow5712, arows5711]
  all_goals rfl

theorem atot5712 : totK PA10K2 A10K2.u5712 = [0, 1126441083102, 5304153913227, 7810195583930, 4119896003876, 694713307265, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5712 = KTree.node A10K2.u5710 (nat_lit 93403990) (nat_lit 8453425429) (nat_lit 0) A10K2.u5711 from rfl, totK_node, atot5710, atot5711]
  decide +kernel

theorem arows5716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5716 = true := by
  rw [show A10K2.u5716 = KTree.node A10K2.u5714 (nat_lit 93418736) (nat_lit 8153552993) (nat_lit 0) A10K2.u5715 from rfl, allE_node, arows5714, irow5716, arows5715]
  all_goals rfl

theorem atot5716 : totK PA10K2 A10K2.u5716 = [0, 461607179050, 3512463926672, 7964826235225, 6079728282978, 1326793549660, 57480818907, 0, 0, 0] := by
  rw [show A10K2.u5716 = KTree.node A10K2.u5714 (nat_lit 93418736) (nat_lit 8153552993) (nat_lit 0) A10K2.u5715 from rfl, totK_node, atot5714, atot5715]
  decide +kernel

theorem arows5719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5719 = true := by
  rw [show A10K2.u5719 = KTree.node A10K2.u5717 (nat_lit 93438724) (nat_lit 12986382215) (nat_lit 0) A10K2.u5718 from rfl, allE_node, arows5717, irow5719, arows5718]
  all_goals rfl

theorem atot5719 : totK PA10K2 A10K2.u5719 = [0, 0, 875473302975, 4924269471136, 8200774221685, 4172940838358, 616726086952, 31082886609, 0, 0] := by
  rw [show A10K2.u5719 = KTree.node A10K2.u5717 (nat_lit 93438724) (nat_lit 12986382215) (nat_lit 0) A10K2.u5718 from rfl, totK_node, atot5717, atot5718]
  decide +kernel

theorem arows5725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5725 = true := by
  rw [show A10K2.u5725 = KTree.node A10K2.u5723 (nat_lit 93456594) (nat_lit 14596955862) (nat_lit 0) A10K2.u5724 from rfl, allE_node, arows5723, irow5725, arows5724]
  all_goals rfl

theorem atot5725 : totK PA10K2 A10K2.u5725 = [0, 742680831591, 3897815320117, 7048473946502, 5348467954044, 1782794606251, 211453747074, 6121173289, 0, 0] := by
  rw [show A10K2.u5725 = KTree.node A10K2.u5723 (nat_lit 93456594) (nat_lit 14596955862) (nat_lit 0) A10K2.u5724 from rfl, totK_node, atot5723, atot5724]
  decide +kernel

theorem arows5728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5728 = true := by
  rw [show A10K2.u5728 = KTree.node A10K2.u5726 (nat_lit 93468394) (nat_lit 12254763382) (nat_lit 0) A10K2.u5727 from rfl, allE_node, arows5726, irow5728, arows5727]
  all_goals rfl

theorem atot5728 : totK PA10K2 A10K2.u5728 = [0, 1290098466979, 5435439425989, 7638892663687, 4036104845718, 683876071030, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5728 = KTree.node A10K2.u5726 (nat_lit 93468394) (nat_lit 12254763382) (nat_lit 0) A10K2.u5727 from rfl, totK_node, atot5726, atot5727]
  decide +kernel

theorem arows5732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5732 = true := by
  rw [show A10K2.u5732 = KTree.node A10K2.u5730 (nat_lit 93487537) (nat_lit 9602706401) (nat_lit 0) A10K2.u5731 from rfl, allE_node, arows5730, irow5732, arows5731]
  all_goals rfl

theorem atot5732 : totK PA10K2 A10K2.u5732 = [0, 311053418201, 3190409020177, 7829624312773, 6227208507750, 1412866358732, 71254002758, 0, 0, 0] := by
  rw [show A10K2.u5732 = KTree.node A10K2.u5730 (nat_lit 93487537) (nat_lit 9602706401) (nat_lit 0) A10K2.u5731 from rfl, totK_node, atot5730, atot5731]
  decide +kernel

theorem arows5735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5735 = true := by
  rw [show A10K2.u5735 = KTree.node A10K2.u5733 (nat_lit 93505758) (nat_lit 8697158219) (nat_lit 0) A10K2.u5734 from rfl, allE_node, arows5733, irow5735, arows5734]
  all_goals rfl

theorem atot5735 : totK PA10K2 A10K2.u5735 = [0, 0, 1432832066668, 6169546342703, 7978065208550, 2949659293141, 349544223837, 6354482628, 0, 0] := by
  rw [show A10K2.u5735 = KTree.node A10K2.u5733 (nat_lit 93505758) (nat_lit 8697158219) (nat_lit 0) A10K2.u5734 from rfl, totK_node, atot5733, atot5734]
  decide +kernel

theorem arows5740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5740 = true := by
  rw [show A10K2.u5740 = KTree.node A10K2.u5738 (nat_lit 93592069) (nat_lit 6584847527) (nat_lit 0) A10K2.u5739 from rfl, allE_node, arows5738, irow5740, arows5739]
  all_goals rfl

theorem atot5740 : totK PA10K2 A10K2.u5740 = [0, 0, 1273910019065, 5510380909767, 7697475390103, 3729213790573, 572773809694, 30818366867, 0, 0] := by
  rw [show A10K2.u5740 = KTree.node A10K2.u5738 (nat_lit 93592069) (nat_lit 6584847527) (nat_lit 0) A10K2.u5739 from rfl, totK_node, atot5738, atot5739]
  decide +kernel

theorem arows5743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5743 = true := by
  rw [show A10K2.u5743 = KTree.node A10K2.u5741 (nat_lit 93614028) (nat_lit 3905795488) (nat_lit 0) A10K2.u5742 from rfl, allE_node, arows5741, irow5743, arows5742]
  all_goals rfl

theorem atot5743 : totK PA10K2 A10K2.u5743 = [0, 0, 1223235544818, 5398103709219, 8054253122223, 3975829360576, 506700368205, 13207830636, 0, 0] := by
  rw [show A10K2.u5743 = KTree.node A10K2.u5741 (nat_lit 93614028) (nat_lit 3905795488) (nat_lit 0) A10K2.u5742 from rfl, totK_node, atot5741, atot5742]
  decide +kernel

theorem arows5747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5747 = true := by
  rw [show A10K2.u5747 = KTree.node A10K2.u5745 (nat_lit 93667939) (nat_lit 3764740548) (nat_lit 0) A10K2.u5746 from rfl, allE_node, arows5745, irow5747, arows5746]
  all_goals rfl

theorem atot5747 : totK PA10K2 A10K2.u5747 = [0, 0, 823490680995, 4729724251679, 8148219478918, 4511452020873, 678127454334, 31452573850, 0, 0] := by
  rw [show A10K2.u5747 = KTree.node A10K2.u5745 (nat_lit 93667939) (nat_lit 3764740548) (nat_lit 0) A10K2.u5746 from rfl, totK_node, atot5745, atot5746]
  decide +kernel

theorem arows5750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5750 = true := by
  rw [show A10K2.u5750 = KTree.node A10K2.u5748 (nat_lit 93716534) (nat_lit 14580792599) (nat_lit 0) A10K2.u5749 from rfl, allE_node, arows5748, irow5750, arows5749]
  all_goals rfl

theorem atot5750 : totK PA10K2 A10K2.u5750 = [0, 0, 1203290571222, 5242687968992, 7779183946579, 4134573646857, 687423764671, 37931615632, 0, 0] := by
  rw [show A10K2.u5750 = KTree.node A10K2.u5748 (nat_lit 93716534) (nat_lit 14580792599) (nat_lit 0) A10K2.u5749 from rfl, totK_node, atot5748, atot5749]
  decide +kernel

theorem arows5758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5758 = true := by
  rw [show A10K2.u5758 = KTree.node A10K2.u5756 (nat_lit 93728211) (nat_lit 10415645920) (nat_lit 0) A10K2.u5757 from rfl, allE_node, arows5756, irow5758, arows5757]
  all_goals rfl

theorem atot5758 : totK PA10K2 A10K2.u5758 = [0, 0, 1015262766210, 4841860587390, 7816047574241, 4374758597404, 723692947542, 36463937579, 0, 0] := by
  rw [show A10K2.u5758 = KTree.node A10K2.u5756 (nat_lit 93728211) (nat_lit 10415645920) (nat_lit 0) A10K2.u5757 from rfl, totK_node, atot5756, atot5757]
  decide +kernel

theorem arows5761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5761 = true := by
  rw [show A10K2.u5761 = KTree.node A10K2.u5759 (nat_lit 93739255) (nat_lit 4741712768) (nat_lit 0) A10K2.u5760 from rfl, allE_node, arows5759, irow5761, arows5760]
  all_goals rfl

theorem atot5761 : totK PA10K2 A10K2.u5761 = [0, 0, 581670111060, 4025086636300, 8107177134126, 5122992266046, 890280561774, 37547833973, 0, 0] := by
  rw [show A10K2.u5761 = KTree.node A10K2.u5759 (nat_lit 93739255) (nat_lit 4741712768) (nat_lit 0) A10K2.u5760 from rfl, totK_node, atot5759, atot5760]
  decide +kernel

theorem arows5765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5765 = true := by
  rw [show A10K2.u5765 = KTree.node A10K2.u5763 (nat_lit 93767602) (nat_lit 13298891833) (nat_lit 0) A10K2.u5764 from rfl, allE_node, arows5763, irow5765, arows5764]
  all_goals rfl

theorem atot5765 : totK PA10K2 A10K2.u5765 = [0, 0, 319364639558, 2188367423434, 6038536186791, 6915852994708, 2683372454380, 347414729890, 6354482628, 0] := by
  rw [show A10K2.u5765 = KTree.node A10K2.u5763 (nat_lit 93767602) (nat_lit 13298891833) (nat_lit 0) A10K2.u5764 from rfl, totK_node, atot5763, atot5764]
  decide +kernel

theorem arows5768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5768 = true := by
  rw [show A10K2.u5768 = KTree.node A10K2.u5766 (nat_lit 94377997) (nat_lit 5811818217) (nat_lit 0) A10K2.u5767 from rfl, allE_node, arows5766, irow5768, arows5767]
  all_goals rfl

theorem atot5768 : totK PA10K2 A10K2.u5768 = [0, 0, 1230273666516, 5263184731744, 7690283033206, 4045056505941, 655166350835, 30831673886, 0, 0] := by
  rw [show A10K2.u5768 = KTree.node A10K2.u5766 (nat_lit 94377997) (nat_lit 5811818217) (nat_lit 0) A10K2.u5767 from rfl, totK_node, atot5766, atot5767]
  decide +kernel

theorem arows5773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5773 = true := by
  rw [show A10K2.u5773 = KTree.node A10K2.u5771 (nat_lit 94398344) (nat_lit 13452125706) (nat_lit 0) A10K2.u5772 from rfl, allE_node, arows5771, irow5773, arows5772]
  all_goals rfl

theorem atot5773 : totK PA10K2 A10K2.u5773 = [0, 0, 652692863706, 4428645304133, 8494081743129, 5211455066887, 776147841504, 19100662535, 0, 0] := by
  rw [show A10K2.u5773 = KTree.node A10K2.u5771 (nat_lit 94398344) (nat_lit 13452125706) (nat_lit 0) A10K2.u5772 from rfl, totK_node, atot5771, atot5772]
  decide +kernel

theorem arows5776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5776 = true := by
  rw [show A10K2.u5776 = KTree.node A10K2.u5774 (nat_lit 94411020) (nat_lit 12085458580) (nat_lit 0) A10K2.u5775 from rfl, allE_node, arows5774, irow5776, arows5775]
  all_goals rfl

theorem atot5776 : totK PA10K2 A10K2.u5776 = [0, 0, 0, 1260797588000, 5791517747845, 7884737179981, 3348394290306, 514625613189, 30650496230, 0] := by
  rw [show A10K2.u5776 = KTree.node A10K2.u5774 (nat_lit 94411020) (nat_lit 12085458580) (nat_lit 0) A10K2.u5775 from rfl, totK_node, atot5774, atot5775]
  decide +kernel

theorem arows5780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5780 = true := by
  rw [show A10K2.u5780 = KTree.node A10K2.u5778 (nat_lit 94503318) (nat_lit 12352457192) (nat_lit 0) A10K2.u5779 from rfl, allE_node, arows5778, irow5780, arows5779]
  all_goals rfl

theorem atot5780 : totK PA10K2 A10K2.u5780 = [0, 0, 778776062315, 3865931150707, 6936258884442, 5560487971267, 1873088560301, 227562793466, 5546304973, 0] := by
  rw [show A10K2.u5780 = KTree.node A10K2.u5778 (nat_lit 94503318) (nat_lit 12352457192) (nat_lit 0) A10K2.u5779 from rfl, totK_node, atot5778, atot5779]
  decide +kernel

theorem arows5783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5783 = true := by
  rw [show A10K2.u5783 = KTree.node A10K2.u5781 (nat_lit 94516891) (nat_lit 10042796836) (nat_lit 0) A10K2.u5782 from rfl, allE_node, arows5781, irow5783, arows5782]
  all_goals rfl

theorem atot5783 : totK PA10K2 A10K2.u5783 = [0, 0, 1248326146823, 5137000421403, 7425745138200, 4154551573261, 716507426297, 36794179553, 0, 0] := by
  rw [show A10K2.u5783 = KTree.node A10K2.u5781 (nat_lit 94516891) (nat_lit 10042796836) (nat_lit 0) A10K2.u5782 from rfl, totK_node, atot5781, atot5782]
  decide +kernel

theorem arows5789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5789 = true := by
  rw [show A10K2.u5789 = KTree.node A10K2.u5787 (nat_lit 94536453) (nat_lit 6876893410) (nat_lit 0) A10K2.u5788 from rfl, allE_node, arows5787, irow5789, arows5788]
  all_goals rfl

theorem atot5789 : totK PA10K2 A10K2.u5789 = [0, 0, 112109183544, 2843220394594, 8004311861191, 6535725693797, 1347261445317, 70818940565, 0, 0] := by
  rw [show A10K2.u5789 = KTree.node A10K2.u5787 (nat_lit 94536453) (nat_lit 6876893410) (nat_lit 0) A10K2.u5788 from rfl, totK_node, atot5787, atot5788]
  decide +kernel

theorem arows5792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5792 = true := by
  rw [show A10K2.u5792 = KTree.node A10K2.u5790 (nat_lit 94557332) (nat_lit 12505876131) (nat_lit 0) A10K2.u5791 from rfl, allE_node, arows5790, irow5792, arows5791]
  all_goals rfl

theorem atot5792 : totK PA10K2 A10K2.u5792 = [0, 0, 770688507529, 3277244086217, 6016585230004, 6014106078392, 2395970405681, 322395268869, 6354482628, 0] := by
  rw [show A10K2.u5792 = KTree.node A10K2.u5790 (nat_lit 94557332) (nat_lit 12505876131) (nat_lit 0) A10K2.u5791 from rfl, totK_node, atot5790, atot5791]
  decide +kernel

theorem arows5796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5796 = true := by
  rw [show A10K2.u5796 = KTree.node A10K2.u5794 (nat_lit 94593640) (nat_lit 11913243854) (nat_lit 0) A10K2.u5795 from rfl, allE_node, arows5794, irow5796, arows5795]
  all_goals rfl

theorem atot5796 : totK PA10K2 A10K2.u5796 = [0, 0, 913753439838, 4766490288307, 8301437471709, 5076353774881, 897024501305, 37664216019, 0, 0] := by
  rw [show A10K2.u5796 = KTree.node A10K2.u5794 (nat_lit 94593640) (nat_lit 11913243854) (nat_lit 0) A10K2.u5795 from rfl, totK_node, atot5794, atot5795]
  decide +kernel

theorem arows5799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5799 = true := by
  rw [show A10K2.u5799 = KTree.node A10K2.u5797 (nat_lit 94975934) (nat_lit 15278244843) (nat_lit 0) A10K2.u5798 from rfl, allE_node, arows5797, irow5799, arows5798]
  all_goals rfl

theorem atot5799 : totK PA10K2 A10K2.u5799 = [0, 0, 1176865707140, 5189972085015, 7754408963215, 4220659948844, 695709386063, 31768748853, 0, 0] := by
  rw [show A10K2.u5799 = KTree.node A10K2.u5797 (nat_lit 94975934) (nat_lit 15278244843) (nat_lit 0) A10K2.u5798 from rfl, totK_node, atot5797, atot5798]
  decide +kernel

theorem arows5804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5804 = true := by
  rw [show A10K2.u5804 = KTree.node A10K2.u5802 (nat_lit 94988130) (nat_lit 12901090530) (nat_lit 0) A10K2.u5803 from rfl, allE_node, arows5802, irow5804, arows5803]
  all_goals rfl

theorem atot5804 : totK PA10K2 A10K2.u5804 = [0, 0, 724045030467, 4552722276996, 8520039111805, 5129761395298, 776227967788, 19280604132, 0, 0] := by
  rw [show A10K2.u5804 = KTree.node A10K2.u5802 (nat_lit 94988130) (nat_lit 12901090530) (nat_lit 0) A10K2.u5803 from rfl, totK_node, atot5802, atot5803]
  decide +kernel

theorem arows5807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5807 = true := by
  rw [show A10K2.u5807 = KTree.node A10K2.u5805 (nat_lit 95009002) (nat_lit 12403245268) (nat_lit 0) A10K2.u5806 from rfl, allE_node, arows5805, irow5807, arows5806]
  all_goals rfl

theorem atot5807 : totK PA10K2 A10K2.u5807 = [0, 0, 0, 1263047550759, 5856398499006, 7936754262277, 3403564212938, 526274847050, 31082886609, 0] := by
  rw [show A10K2.u5807 = KTree.node A10K2.u5805 (nat_lit 95009002) (nat_lit 12403245268) (nat_lit 0) A10K2.u5806 from rfl, totK_node, atot5805, atot5806]
  decide +kernel

theorem arows5811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5811 = true := by
  rw [show A10K2.u5811 = KTree.node A10K2.u5809 (nat_lit 95027654) (nat_lit 13771498930) (nat_lit 0) A10K2.u5810 from rfl, allE_node, arows5809, irow5811, arows5810]
  all_goals rfl

theorem atot5811 : totK PA10K2 A10K2.u5811 = [0, 0, 726863936490, 3531952842691, 6581320821662, 5768861750235, 2045584409846, 240376777320, 6121173289, 0] := by
  rw [show A10K2.u5811 = KTree.node A10K2.u5809 (nat_lit 95027654) (nat_lit 13771498930) (nat_lit 0) A10K2.u5810 from rfl, totK_node, atot5809, atot5810]
  decide +kernel

theorem arows5814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5814 = true := by
  rw [show A10K2.u5814 = KTree.node A10K2.u5812 (nat_lit 95041464) (nat_lit 2963235294) (nat_lit 128) A10K2.u5813 from rfl, allE_node, arows5812, irow5814, arows5813]
  all_goals rfl

theorem atot5814 : totK PA10K2 A10K2.u5814 = [0, 0, 1306342038829, 5489719905675, 7704555613866, 4021221308556, 631516906614, 31768748853, 0, 0] := by
  rw [show A10K2.u5814 = KTree.node A10K2.u5812 (nat_lit 95041464) (nat_lit 2963235294) (nat_lit 128) A10K2.u5813 from rfl, totK_node, atot5812, atot5813]
  decide +kernel

theorem arows5821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5821 = true := by
  rw [show A10K2.u5821 = KTree.node A10K2.u5819 (nat_lit 95060800) (nat_lit 14462861641) (nat_lit 0) A10K2.u5820 from rfl, allE_node, arows5819, irow5821, arows5820]
  all_goals rfl

theorem atot5821 : totK PA10K2 A10K2.u5821 = [0, 0, 112111361307, 2840492144496, 7992598800825, 6536171840414, 1382976262901, 70383685680, 0, 0] := by
  rw [show A10K2.u5821 = KTree.node A10K2.u5819 (nat_lit 95060800) (nat_lit 14462861641) (nat_lit 0) A10K2.u5820 from rfl, totK_node, atot5819, atot5820]
  decide +kernel

theorem arows5824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5824 = true := by
  rw [show A10K2.u5824 = KTree.node A10K2.u5822 (nat_lit 95081637) (nat_lit 7146558338) (nat_lit 0) A10K2.u5823 from rfl, allE_node, arows5822, irow5824, arows5823]
  all_goals rfl

theorem atot5824 : totK PA10K2 A10K2.u5824 = [0, 0, 773889436601, 3303254945654, 6074658416020, 6044555936310, 2370647509150, 322913992912, 6354482628, 0] := by
  rw [show A10K2.u5824 = KTree.node A10K2.u5822 (nat_lit 95081637) (nat_lit 7146558338) (nat_lit 0) A10K2.u5823 from rfl, totK_node, atot5822, atot5823]
  decide +kernel

theorem arows5828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5828 = true := by
  rw [show A10K2.u5828 = KTree.node A10K2.u5826 (nat_lit 95119070) (nat_lit 10313950122) (nat_lit 0) A10K2.u5827 from rfl, allE_node, arows5826, irow5828, arows5827]
  all_goals rfl

theorem atot5828 : totK PA10K2 A10K2.u5828 = [0, 0, 902592212713, 4715657303135, 8278542382975, 5233373726723, 926068104763, 38484975863, 0, 0] := by
  rw [show A10K2.u5828 = KTree.node A10K2.u5826 (nat_lit 95119070) (nat_lit 10313950122) (nat_lit 0) A10K2.u5827 from rfl, totK_node, atot5826, atot5827]
  decide +kernel

theorem arows5831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5831 = true := by
  rw [show A10K2.u5831 = KTree.node A10K2.u5829 (nat_lit 95426714) (nat_lit 13417331109) (nat_lit 0) A10K2.u5830 from rfl, allE_node, arows5829, irow5831, arows5830]
  all_goals rfl

theorem atot5831 : totK PA10K2 A10K2.u5831 = [0, 0, 1269947970051, 5447492217683, 7698516796581, 3879006346871, 600975131360, 30831673886, 0, 0] := by
  rw [show A10K2.u5831 = KTree.node A10K2.u5829 (nat_lit 95426714) (nat_lit 13417331109) (nat_lit 0) A10K2.u5830 from rfl, totK_node, atot5829, atot5830]
  decide +kernel

theorem arows5836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5836 = true := by
  rw [show A10K2.u5836 = KTree.node A10K2.u5834 (nat_lit 95449097) (nat_lit 9788426220) (nat_lit 0) A10K2.u5835 from rfl, allE_node, arows5834, irow5836, arows5835]
  all_goals rfl

theorem atot5836 : totK PA10K2 A10K2.u5836 = [0, 0, 458520426296, 3719473812599, 8166146620930, 5668929340178, 989070086196, 44430242113, 0, 0] := by
  rw [show A10K2.u5836 = KTree.node A10K2.u5834 (nat_lit 95449097) (nat_lit 9788426220) (nat_lit 0) A10K2.u5835 from rfl, totK_node, atot5834, atot5835]
  decide +kernel

theorem arows5839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5839 = true := by
  rw [show A10K2.u5839 = KTree.node A10K2.u5837 (nat_lit 95470802) (nat_lit 15466181898) (nat_lit 0) A10K2.u5838 from rfl, allE_node, arows5837, irow5839, arows5838]
  all_goals rfl

theorem atot5839 : totK PA10K2 A10K2.u5839 = [0, 0, 0, 960000781662, 4987150217768, 7879232118792, 3923115555465, 672674144362, 35767183343, 0] := by
  rw [show A10K2.u5839 = KTree.node A10K2.u5837 (nat_lit 95470802) (nat_lit 15466181898) (nat_lit 0) A10K2.u5838 from rfl, totK_node, atot5837, atot5838]
  decide +kernel

theorem arows5843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5843 = true := by
  rw [show A10K2.u5843 = KTree.node A10K2.u5841 (nat_lit 95497947) (nat_lit 6873333145) (nat_lit 0) A10K2.u5842 from rfl, allE_node, arows5841, irow5843, arows5842]
  all_goals rfl

theorem atot5843 : totK PA10K2 A10K2.u5843 = [0, 0, 1112555489502, 4913057106496, 7664781493462, 4620438339873, 774711513770, 41325607053, 0, 0] := by
  rw [show A10K2.u5843 = KTree.node A10K2.u5841 (nat_lit 95497947) (nat_lit 6873333145) (nat_lit 0) A10K2.u5842 from rfl, totK_node, atot5841, atot5842]
  decide +kernel

theorem arows5846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5846 = true := by
  rw [show A10K2.u5846 = KTree.node A10K2.u5844 (nat_lit 95509152) (nat_lit 8336744061) (nat_lit 0) A10K2.u5845 from rfl, allE_node, arows5844, irow5846, arows5845]
  all_goals rfl

theorem atot5846 : totK PA10K2 A10K2.u5846 = [0, 0, 930250018933, 4936241759596, 8203487714588, 4513444508144, 679669468031, 28519990413, 0, 0] := by
  rw [show A10K2.u5846 = KTree.node A10K2.u5844 (nat_lit 95509152) (nat_lit 8336744061) (nat_lit 0) A10K2.u5845 from rfl, totK_node, atot5844, atot5845]
  decide +kernel

theorem arows5852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5852 = true := by
  rw [show A10K2.u5852 = KTree.node A10K2.u5850 (nat_lit 95533831) (nat_lit 765579859) (nat_lit 0) A10K2.u5851 from rfl, allE_node, arows5850, irow5852, arows5851]
  all_goals rfl

theorem atot5852 : totK PA10K2 A10K2.u5852 = [0, 0, 0, 1267332393168, 5809728955278, 7848216275894, 3250110247998, 519029652847, 30647824416, 0] := by
  rw [show A10K2.u5852 = KTree.node A10K2.u5850 (nat_lit 95533831) (nat_lit 765579859) (nat_lit 0) A10K2.u5851 from rfl, totK_node, atot5850, atot5851]
  decide +kernel

theorem arows5855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5855 = true := by
  rw [show A10K2.u5855 = KTree.node A10K2.u5853 (nat_lit 95552355) (nat_lit 4947214961) (nat_lit 0) A10K2.u5854 from rfl, allE_node, arows5853, irow5855, arows5854]
  all_goals rfl

theorem atot5855 : totK PA10K2 A10K2.u5855 = [0, 0, 733026072910, 3664626088837, 6785771465036, 5489827508705, 1843313216272, 241668834741, 6121173289, 0] := by
  rw [show A10K2.u5855 = KTree.node A10K2.u5853 (nat_lit 95552355) (nat_lit 4947214961) (nat_lit 0) A10K2.u5854 from rfl, totK_node, atot5853, atot5854]
  decide +kernel

theorem arows5859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5859 = true := by
  rw [show A10K2.u5859 = KTree.node A10K2.u5857 (nat_lit 95565275) (nat_lit 6868049882) (nat_lit 0) A10K2.u5858 from rfl, allE_node, arows5857, irow5859, arows5858]
  all_goals rfl

theorem atot5859 : totK PA10K2 A10K2.u5859 = [0, 0, 1273577466899, 5371400220187, 7498900677422, 3966408613419, 699848831381, 37229241746, 0, 0] := by
  rw [show A10K2.u5859 = KTree.node A10K2.u5857 (nat_lit 95565275) (nat_lit 6868049882) (nat_lit 0) A10K2.u5858 from rfl, totK_node, atot5857, atot5858]
  decide +kernel

theorem arows5862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5862 = true := by
  rw [show A10K2.u5862 = KTree.node A10K2.u5860 (nat_lit 95584526) (nat_lit 10788804249) (nat_lit 0) A10K2.u5861 from rfl, allE_node, arows5860, irow5862, arows5861]
  all_goals rfl

theorem atot5862 : totK PA10K2 A10K2.u5862 = [0, 0, 311053418201, 3223430839079, 7829946700695, 6073565297976, 1297658738800, 70822948407, 0, 0] := by
  rw [show A10K2.u5862 = KTree.node A10K2.u5860 (nat_lit 95584526) (nat_lit 10788804249) (nat_lit 0) A10K2.u5861 from rfl, totK_node, atot5860, atot5861]
  decide +kernel

theorem arows5867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5867 = true := by
  rw [show A10K2.u5867 = KTree.node A10K2.u5865 (nat_lit 95602867) (nat_lit 9882314141) (nat_lit 0) A10K2.u5866 from rfl, allE_node, arows5865, irow5867, arows5866]
  all_goals rfl

theorem atot5867 : totK PA10K2 A10K2.u5867 = [0, 0, 0, 1483016879162, 6235491027241, 7793386232540, 2850092828710, 349106822165, 6354482628, 0] := by
  rw [show A10K2.u5867 = KTree.node A10K2.u5865 (nat_lit 95602867) (nat_lit 9882314141) (nat_lit 0) A10K2.u5866 from rfl, totK_node, atot5865, atot5866]
  decide +kernel

theorem arows5870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5870 = true := by
  rw [show A10K2.u5870 = KTree.node A10K2.u5868 (nat_lit 95689495) (nat_lit 941977810) (nat_lit 0) A10K2.u5869 from rfl, allE_node, arows5868, irow5870, arows5869]
  all_goals rfl

theorem atot5870 : totK PA10K2 A10K2.u5870 = [0, 0, 0, 1263527396879, 5641620723414, 7857706984329, 3439809255979, 544155108283, 30388749007, 0] := by
  rw [show A10K2.u5870 = KTree.node A10K2.u5868 (nat_lit 95689495) (nat_lit 941977810) (nat_lit 0) A10K2.u5869 from rfl, totK_node, atot5868, atot5869]
  decide +kernel

theorem arows5874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5874 = true := by
  rw [show A10K2.u5874 = KTree.node A10K2.u5872 (nat_lit 95758081) (nat_lit 7137730441) (nat_lit 0) A10K2.u5873 from rfl, allE_node, arows5872, irow5874, arows5873]
  all_goals rfl

theorem atot5874 : totK PA10K2 A10K2.u5874 = [0, 0, 0, 1257853774178, 5460586567877, 7767187796969, 3736218879442, 647167128865, 31653953727, 0] := by
  rw [show A10K2.u5874 = KTree.node A10K2.u5872 (nat_lit 95758081) (nat_lit 7137730441) (nat_lit 0) A10K2.u5873 from rfl, totK_node, atot5872, atot5873]
  decide +kernel

theorem arows5877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5877 = true := by
  rw [show A10K2.u5877 = KTree.node A10K2.u5875 (nat_lit 95768940) (nat_lit 12674247042) (nat_lit 0) A10K2.u5876 from rfl, allE_node, arows5875, irow5877, arows5876]
  all_goals rfl

theorem atot5877 : totK PA10K2 A10K2.u5877 = [0, 0, 0, 1523085645333, 6184614248850, 7622803706016, 3168222205352, 469750005673, 12072523186, 0] := by
  rw [show A10K2.u5877 = KTree.node A10K2.u5875 (nat_lit 95768940) (nat_lit 12674247042) (nat_lit 0) A10K2.u5876 from rfl, totK_node, atot5875, atot5876]
  decide +kernel

theorem arows5886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5886 = true := by
  rw [show A10K2.u5886 = KTree.node A10K2.u5884 (nat_lit 95820812) (nat_lit 10217015745) (nat_lit 0) A10K2.u5885 from rfl, allE_node, arows5884, irow5886, arows5885]
  all_goals rfl

theorem atot5886 : totK PA10K2 A10K2.u5886 = [0, 0, 0, 1178577887773, 5217980778457, 7617429717203, 3803593634525, 710640138249, 49650489499, 0] := by
  rw [show A10K2.u5886 = KTree.node A10K2.u5884 (nat_lit 95820812) (nat_lit 10217015745) (nat_lit 0) A10K2.u5885 from rfl, totK_node, atot5884, atot5885]
  decide +kernel

theorem arows5889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5889 = true := by
  rw [show A10K2.u5889 = KTree.node A10K2.u5887 (nat_lit 95832282) (nat_lit 14025086665) (nat_lit 0) A10K2.u5888 from rfl, allE_node, arows5887, irow5889, arows5888]
  all_goals rfl

theorem atot5889 : totK PA10K2 A10K2.u5889 = [0, 0, 0, 840509865074, 4603958643396, 7954290789925, 4398998850978, 754082299365, 37235076301, 0] := by
  rw [show A10K2.u5889 = KTree.node A10K2.u5887 (nat_lit 95832282) (nat_lit 14025086665) (nat_lit 0) A10K2.u5888 from rfl, totK_node, atot5887, atot5888]
  decide +kernel

theorem arows5893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5893 = true := by
  rw [show A10K2.u5893 = KTree.node A10K2.u5891 (nat_lit 95862832) (nat_lit 14676329589) (nat_lit 0) A10K2.u5892 from rfl, allE_node, arows5891, irow5893, arows5892]
  all_goals rfl

theorem atot5893 : totK PA10K2 A10K2.u5893 = [0, 0, 0, 0, 1997400299480, 7075813941714, 7029598943728, 2031708482331, 145512412850, 0] := by
  rw [show A10K2.u5893 = KTree.node A10K2.u5891 (nat_lit 95862832) (nat_lit 14676329589) (nat_lit 0) A10K2.u5892 from rfl, totK_node, atot5891, atot5892]
  decide +kernel

theorem arows5896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5896 = true := by
  rw [show A10K2.u5896 = KTree.node A10K2.u5894 (nat_lit 100666781) (nat_lit 1036000720) (nat_lit 0) A10K2.u5895 from rfl, allE_node, arows5894, irow5896, arows5895]
  all_goals rfl

theorem atot5896 : totK PA10K2 A10K2.u5896 = [1058637277771, 4454015480509, 6525423530273, 3602832728812, 635163855492, 405095262212, 1233212591026, 990914908768, 213642913445, 6354482628] := by
  rw [show A10K2.u5896 = KTree.node A10K2.u5894 (nat_lit 100666781) (nat_lit 1036000720) (nat_lit 0) A10K2.u5895 from rfl, totK_node, atot5894, atot5895]
  decide +kernel

theorem arows5901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5901 = true := by
  rw [show A10K2.u5901 = KTree.node A10K2.u5899 (nat_lit 100686125) (nat_lit 6651382109) (nat_lit 0) A10K2.u5900 from rfl, allE_node, arows5899, irow5901, arows5900]
  all_goals rfl

theorem atot5901 : totK PA10K2 A10K2.u5901 = [1269857319490, 5796887834334, 8046376224566, 3512920717097, 401325513629, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u5901 = KTree.node A10K2.u5899 (nat_lit 100686125) (nat_lit 6651382109) (nat_lit 0) A10K2.u5900 from rfl, totK_node, atot5899, atot5900]
  decide +kernel

theorem arows5904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5904 = true := by
  rw [show A10K2.u5904 = KTree.node A10K2.u5902 (nat_lit 100696986) (nat_lit 9144855638) (nat_lit 0) A10K2.u5903 from rfl, allE_node, arows5902, irow5904, arows5903]
  all_goals rfl

theorem atot5904 : totK PA10K2 A10K2.u5904 = [0, 1498181530633, 6243095083782, 8015483262240, 3259872599196, 478812952777, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u5904 = KTree.node A10K2.u5902 (nat_lit 100696986) (nat_lit 9144855638) (nat_lit 0) A10K2.u5903 from rfl, totK_node, atot5902, atot5903]
  decide +kernel

theorem arows5908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5908 = true := by
  rw [show A10K2.u5908 = KTree.node A10K2.u5906 (nat_lit 100716800) (nat_lit 14814158032) (nat_lit 0) A10K2.u5907 from rfl, allE_node, arows5906, irow5908, arows5907]
  all_goals rfl

theorem atot5908 : totK PA10K2 A10K2.u5908 = [0, 1464371873892, 5953963621452, 7698194947270, 3332467939000, 422582766876, 10957026886, 0, 0, 0] := by
  rw [show A10K2.u5908 = KTree.node A10K2.u5906 (nat_lit 100716800) (nat_lit 14814158032) (nat_lit 0) A10K2.u5907 from rfl, totK_node, atot5906, atot5907]
  decide +kernel

theorem arows5911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5911 = true := by
  rw [show A10K2.u5911 = KTree.node A10K2.u5909 (nat_lit 100798497) (nat_lit 10204605750) (nat_lit 0) A10K2.u5910 from rfl, allE_node, arows5909, irow5911, arows5910]
  all_goals rfl

theorem atot5911 : totK PA10K2 A10K2.u5911 = [1047365728931, 4812764668684, 7527800390183, 4742426744993, 1167392630045, 81131871664, 0, 0, 0, 0] := by
  rw [show A10K2.u5911 = KTree.node A10K2.u5909 (nat_lit 100798497) (nat_lit 10204605750) (nat_lit 0) A10K2.u5910 from rfl, totK_node, atot5909, atot5910]
  decide +kernel

theorem arows5917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5917 = true := by
  rw [show A10K2.u5917 = KTree.node A10K2.u5915 (nat_lit 100815188) (nat_lit 12930832189) (nat_lit 0) A10K2.u5916 from rfl, allE_node, arows5915, irow5917, arows5916]
  all_goals rfl

theorem atot5917 : totK PA10K2 A10K2.u5917 = [742419772272, 4088047479935, 7650514155949, 5233466900366, 1036165610970, 44376575138, 0, 0, 0, 0] := by
  rw [show A10K2.u5917 = KTree.node A10K2.u5915 (nat_lit 100815188) (nat_lit 12930832189) (nat_lit 0) A10K2.u5916 from rfl, totK_node, atot5915, atot5916]
  decide +kernel

theorem arows5920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5920 = true := by
  rw [show A10K2.u5920 = KTree.node A10K2.u5918 (nat_lit 100845786) (nat_lit 13593433970) (nat_lit 0) A10K2.u5919 from rfl, allE_node, arows5918, irow5920, arows5919]
  all_goals rfl

theorem atot5920 : totK PA10K2 A10K2.u5920 = [338679903066, 2309962325647, 6269913028732, 7000151002242, 2665807063084, 329190577189, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5920 = KTree.node A10K2.u5918 (nat_lit 100845786) (nat_lit 13593433970) (nat_lit 0) A10K2.u5919 from rfl, totK_node, atot5918, atot5919]
  decide +kernel

theorem arows5924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5924 = true := by
  rw [show A10K2.u5924 = KTree.node A10K2.u5922 (nat_lit 100866922) (nat_lit 5456674763) (nat_lit 0) A10K2.u5923 from rfl, allE_node, arows5922, irow5924, arows5923]
  all_goals rfl

theorem atot5924 : totK PA10K2 A10K2.u5924 = [984157656490, 4977737437604, 8235888499561, 4949255992784, 920085151247, 50481587014, 0, 0, 0, 0] := by
  rw [show A10K2.u5924 = KTree.node A10K2.u5922 (nat_lit 100866922) (nat_lit 5456674763) (nat_lit 0) A10K2.u5923 from rfl, totK_node, atot5922, atot5923]
  decide +kernel

theorem arows5927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5927 = true := by
  rw [show A10K2.u5927 = KTree.node A10K2.u5925 (nat_lit 100888902) (nat_lit 10914992213) (nat_lit 0) A10K2.u5926 from rfl, allE_node, arows5925, irow5927, arows5926]
  all_goals rfl

theorem atot5927 : totK PA10K2 A10K2.u5927 = [845700278790, 4310670291115, 7800132503861, 5696109786097, 1394404143168, 83145843390, 0, 0, 0, 0] := by
  rw [show A10K2.u5927 = KTree.node A10K2.u5925 (nat_lit 100888902) (nat_lit 10914992213) (nat_lit 0) A10K2.u5926 from rfl, totK_node, atot5925, atot5926]
  decide +kernel

theorem arows5932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5932 = true := by
  rw [show A10K2.u5932 = KTree.node A10K2.u5930 (nat_lit 100899998) (nat_lit 15136420164) (nat_lit 0) A10K2.u5931 from rfl, allE_node, arows5930, irow5932, arows5931]
  all_goals rfl

theorem atot5932 : totK PA10K2 A10K2.u5932 = [0, 1094850003148, 5258250881138, 8413319626681, 4649723276723, 675594806044, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u5932 = KTree.node A10K2.u5930 (nat_lit 100899998) (nat_lit 15136420164) (nat_lit 0) A10K2.u5931 from rfl, totK_node, atot5930, atot5931]
  decide +kernel

theorem arows5935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5935 = true := by
  rw [show A10K2.u5935 = KTree.node A10K2.u5933 (nat_lit 100921891) (nat_lit 757317843) (nat_lit 0) A10K2.u5934 from rfl, allE_node, arows5933, irow5935, arows5934]
  all_goals rfl

theorem atot5935 : totK PA10K2 A10K2.u5935 = [0, 1177682815167, 5204529484392, 7786596512821, 4708492799973, 1015923958655, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u5935 = KTree.node A10K2.u5933 (nat_lit 100921891) (nat_lit 757317843) (nat_lit 0) A10K2.u5934 from rfl, totK_node, atot5933, atot5934]
  decide +kernel

theorem arows5939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5939 = true := by
  rw [show A10K2.u5939 = KTree.node A10K2.u5937 (nat_lit 100932133) (nat_lit 7149674874) (nat_lit 0) A10K2.u5938 from rfl, allE_node, arows5937, irow5939, arows5938]
  all_goals rfl

theorem atot5939 : totK PA10K2 A10K2.u5939 = [0, 1121573921595, 5230766651402, 7796565531852, 3977673387597, 649862177434, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5939 = KTree.node A10K2.u5937 (nat_lit 100932133) (nat_lit 7149674874) (nat_lit 0) A10K2.u5938 from rfl, totK_node, atot5937, atot5938]
  decide +kernel

theorem arows5942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5942 = true := by
  rw [show A10K2.u5942 = KTree.node A10K2.u5940 (nat_lit 100953493) (nat_lit 2219627532) (nat_lit 0) A10K2.u5941 from rfl, allE_node, arows5940, irow5942, arows5941]
  all_goals rfl

theorem atot5942 : totK PA10K2 A10K2.u5942 = [0, 786135904618, 4450550014323, 8203339349117, 5192960946591, 941179209405, 40736193832, 0, 0, 0] := by
  rw [show A10K2.u5942 = KTree.node A10K2.u5940 (nat_lit 100953493) (nat_lit 2219627532) (nat_lit 0) A10K2.u5941 from rfl, totK_node, atot5940, atot5941]
  decide +kernel

theorem arows5949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5949 = true := by
  rw [show A10K2.u5949 = KTree.node A10K2.u5947 (nat_lit 100963168) (nat_lit 12571607869) (nat_lit 0) A10K2.u5948 from rfl, allE_node, arows5947, irow5949, arows5948]
  all_goals rfl

theorem atot5949 : totK PA10K2 A10K2.u5949 = [0, 0, 1319493438354, 5571125387457, 7492779799849, 3511104232949, 606613734588, 30605747850, 0, 0] := by
  rw [show A10K2.u5949 = KTree.node A10K2.u5947 (nat_lit 100963168) (nat_lit 12571607869) (nat_lit 0) A10K2.u5948 from rfl, totK_node, atot5947, atot5948]
  decide +kernel

theorem arows5952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5952 = true := by
  rw [show A10K2.u5952 = KTree.node A10K2.u5950 (nat_lit 100986074) (nat_lit 11812177365) (nat_lit 0) A10K2.u5951 from rfl, allE_node, arows5950, irow5952, arows5951]
  all_goals rfl

theorem atot5952 : totK PA10K2 A10K2.u5952 = [0, 795232957208, 3681707061209, 6602607797552, 5815884688408, 2082298976761, 240688322013, 5528811039, 0, 0] := by
  rw [show A10K2.u5952 = KTree.node A10K2.u5950 (nat_lit 100986074) (nat_lit 11812177365) (nat_lit 0) A10K2.u5951 from rfl, totK_node, atot5950, atot5951]
  decide +kernel

theorem arows5956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5956 = true := by
  rw [show A10K2.u5956 = KTree.node A10K2.u5954 (nat_lit 101071105) (nat_lit 9770762046) (nat_lit 0) A10K2.u5955 from rfl, allE_node, arows5954, irow5956, arows5955]
  all_goals rfl

theorem atot5956 : totK PA10K2 A10K2.u5956 = [0, 993426424225, 4832244285786, 7675927419710, 4431542969621, 804189040553, 36865889447, 0, 0, 0] := by
  rw [show A10K2.u5956 = KTree.node A10K2.u5954 (nat_lit 101071105) (nat_lit 9770762046) (nat_lit 0) A10K2.u5955 from rfl, totK_node, atot5954, atot5955]
  decide +kernel

theorem arows5959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5959 = true := by
  rw [show A10K2.u5959 = KTree.node A10K2.u5957 (nat_lit 101092205) (nat_lit 6122794295) (nat_lit 0) A10K2.u5958 from rfl, allE_node, arows5957, irow5959, arows5958]
  all_goals rfl

theorem atot5959 : totK PA10K2 A10K2.u5959 = [0, 0, 2220620552038, 7666152946162, 7106536335819, 1641168289658, 81783304252, 0, 0, 0] := by
  rw [show A10K2.u5959 = KTree.node A10K2.u5957 (nat_lit 101092205) (nat_lit 6122794295) (nat_lit 0) A10K2.u5958 from rfl, totK_node, atot5957, atot5958]
  decide +kernel

theorem arows5964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5964 = true := by
  rw [show A10K2.u5964 = KTree.node A10K2.u5962 (nat_lit 101124371) (nat_lit 3586309044) (nat_lit 0) A10K2.u5963 from rfl, allE_node, arows5962, irow5964, arows5963]
  all_goals rfl

theorem atot5964 : totK PA10K2 A10K2.u5964 = [0, 807311024672, 3830668021360, 6907460796114, 5518147344337, 1844131279909, 217603257819, 5676195732, 0, 0] := by
  rw [show A10K2.u5964 = KTree.node A10K2.u5962 (nat_lit 101124371) (nat_lit 3586309044) (nat_lit 0) A10K2.u5963 from rfl, totK_node, atot5962, atot5963]
  decide +kernel

theorem arows5967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5967 = true := by
  rw [show A10K2.u5967 = KTree.node A10K2.u5965 (nat_lit 101147026) (nat_lit 13900687015) (nat_lit 0) A10K2.u5966 from rfl, allE_node, arows5965, irow5967, arows5966]
  all_goals rfl

theorem atot5967 : totK PA10K2 A10K2.u5967 = [0, 1356831199287, 5793833625629, 8293752599478, 4323670082424, 655685545642, 14004528958, 0, 0, 0] := by
  rw [show A10K2.u5967 = KTree.node A10K2.u5965 (nat_lit 101147026) (nat_lit 13900687015) (nat_lit 0) A10K2.u5966 from rfl, totK_node, atot5965, atot5966]
  decide +kernel

theorem arows5971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5971 = true := by
  rw [show A10K2.u5971 = KTree.node A10K2.u5969 (nat_lit 101714195) (nat_lit 9366280227) (nat_lit 0) A10K2.u5970 from rfl, allE_node, arows5969, irow5971, arows5970]
  all_goals rfl

theorem atot5971 : totK PA10K2 A10K2.u5971 = [839403861465, 3698565414690, 6039175918117, 5146464026504, 2888502398008, 789895124273, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u5971 = KTree.node A10K2.u5969 (nat_lit 101714195) (nat_lit 9366280227) (nat_lit 0) A10K2.u5970 from rfl, totK_node, atot5969, atot5970]
  decide +kernel

theorem arows5974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5974 = true := by
  rw [show A10K2.u5974 = KTree.node A10K2.u5972 (nat_lit 101732707) (nat_lit 8407495372) (nat_lit 0) A10K2.u5973 from rfl, allE_node, arows5972, irow5974, arows5973]
  all_goals rfl

theorem atot5974 : totK PA10K2 A10K2.u5974 = [1343077793455, 5846359455609, 8132831084612, 3650884682436, 419428348353, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u5974 = KTree.node A10K2.u5972 (nat_lit 101732707) (nat_lit 8407495372) (nat_lit 0) A10K2.u5973 from rfl, totK_node, atot5972, atot5973]
  decide +kernel

theorem arows5980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5980 = true := by
  rw [show A10K2.u5980 = KTree.node A10K2.u5978 (nat_lit 101746861) (nat_lit 6508178193) (nat_lit 0) A10K2.u5979 from rfl, allE_node, arows5978, irow5980, arows5979]
  all_goals rfl

theorem atot5980 : totK PA10K2 A10K2.u5980 = [0, 1427518805899, 5892695532250, 7791756574725, 3602908374185, 604637575486, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u5980 = KTree.node A10K2.u5978 (nat_lit 101746861) (nat_lit 6508178193) (nat_lit 0) A10K2.u5979 from rfl, totK_node, atot5978, atot5979]
  decide +kernel

theorem arows5983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5983 = true := by
  rw [show A10K2.u5983 = KTree.node A10K2.u5981 (nat_lit 101765575) (nat_lit 10395480199) (nat_lit 0) A10K2.u5982 from rfl, allE_node, arows5981, irow5983, arows5982]
  all_goals rfl

theorem atot5983 : totK PA10K2 A10K2.u5983 = [152930188526, 1692993188945, 6021195509722, 7896034971164, 3230942682622, 333509922940, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u5983 = KTree.node A10K2.u5981 (nat_lit 101765575) (nat_lit 10395480199) (nat_lit 0) A10K2.u5982 from rfl, totK_node, atot5981, atot5982]
  decide +kernel

theorem arows5987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5987 = true := by
  rw [show A10K2.u5987 = KTree.node A10K2.u5985 (nat_lit 101847994) (nat_lit 5157980489) (nat_lit 0) A10K2.u5986 from rfl, allE_node, arows5985, irow5987, arows5986]
  all_goals rfl

theorem atot5987 : totK PA10K2 A10K2.u5987 = [1174112902601, 5448417120157, 7952415981022, 4015466200567, 667953318305, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u5987 = KTree.node A10K2.u5985 (nat_lit 101847994) (nat_lit 5157980489) (nat_lit 0) A10K2.u5986 from rfl, totK_node, atot5985, atot5986]
  decide +kernel

theorem arows5990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5990 = true := by
  rw [show A10K2.u5990 = KTree.node A10K2.u5988 (nat_lit 101861384) (nat_lit 14147002429) (nat_lit 0) A10K2.u5989 from rfl, allE_node, arows5988, irow5990, arows5989]
  all_goals rfl

theorem atot5990 : totK PA10K2 A10K2.u5990 = [820507623861, 4447633766591, 7896855701765, 4877414768769, 869726025331, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u5990 = KTree.node A10K2.u5988 (nat_lit 101861384) (nat_lit 14147002429) (nat_lit 0) A10K2.u5989 from rfl, totK_node, atot5988, atot5989]
  decide +kernel

theorem arows5995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5995 = true := by
  rw [show A10K2.u5995 = KTree.node A10K2.u5993 (nat_lit 101886237) (nat_lit 6421608984) (nat_lit 0) A10K2.u5994 from rfl, allE_node, arows5993, irow5995, arows5994]
  all_goals rfl

theorem atot5995 : totK PA10K2 A10K2.u5995 = [0, 1842000282675, 7107181813303, 7826832550877, 2178522738397, 127877740631, 0, 0, 0, 0] := by
  rw [show A10K2.u5995 = KTree.node A10K2.u5993 (nat_lit 101886237) (nat_lit 6421608984) (nat_lit 0) A10K2.u5994 from rfl, totK_node, atot5993, atot5994]
  decide +kernel

theorem arows5998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5998 = true := by
  rw [show A10K2.u5998 = KTree.node A10K2.u5996 (nat_lit 101976738) (nat_lit 11258600701) (nat_lit 0) A10K2.u5997 from rfl, allE_node, arows5996, irow5998, arows5997]
  all_goals rfl

theorem atot5998 : totK PA10K2 A10K2.u5998 = [0, 839403861465, 4565120193119, 7993127028816, 4664619982355, 835702054158, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u5998 = KTree.node A10K2.u5996 (nat_lit 101976738) (nat_lit 11258600701) (nat_lit 0) A10K2.u5997 from rfl, totK_node, atot5996, atot5997]
  decide +kernel

theorem arows6002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6002 = true := by
  rw [show A10K2.u6002 = KTree.node A10K2.u6000 (nat_lit 101995756) (nat_lit 11606420549) (nat_lit 0) A10K2.u6001 from rfl, allE_node, arows6000, irow6002, arows6001]
  all_goals rfl

theorem atot6002 : totK PA10K2 A10K2.u6002 = [0, 1343077793455, 5786092863019, 8044137080528, 3702871262505, 446298750855, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6002 = KTree.node A10K2.u6000 (nat_lit 101995756) (nat_lit 11606420549) (nat_lit 0) A10K2.u6001 from rfl, totK_node, atot6000, atot6001]
  decide +kernel

theorem arows6005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6005 = true := by
  rw [show A10K2.u6005 = KTree.node A10K2.u6003 (nat_lit 102108601) (nat_lit 7083371331) (nat_lit 0) A10K2.u6004 from rfl, allE_node, arows6003, irow6005, arows6004]
  all_goals rfl

theorem atot6005 : totK PA10K2 A10K2.u6005 = [0, 1043226154395, 4950518506800, 7970764081455, 4539419326771, 763490599976, 36928231554, 0, 0, 0] := by
  rw [show A10K2.u6005 = KTree.node A10K2.u6003 (nat_lit 102108601) (nat_lit 7083371331) (nat_lit 0) A10K2.u6004 from rfl, totK_node, atot6003, atot6004]
  decide +kernel

theorem arows6013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6013 = true := by
  rw [show A10K2.u6013 = KTree.node A10K2.u6011 (nat_lit 102122024) (nat_lit 12594929656) (nat_lit 0) A10K2.u6012 from rfl, allE_node, arows6011, irow6013, arows6012]
  all_goals rfl

theorem atot6013 : totK PA10K2 A10K2.u6013 = [0, 1101717613284, 5229913920503, 7861121866055, 3967100155137, 609278358579, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u6013 = KTree.node A10K2.u6011 (nat_lit 102122024) (nat_lit 12594929656) (nat_lit 0) A10K2.u6012 from rfl, totK_node, atot6011, atot6012]
  decide +kernel

theorem arows6016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6016 = true := by
  rw [show A10K2.u6016 = KTree.node A10K2.u6014 (nat_lit 102147478) (nat_lit 13918161593) (nat_lit 0) A10K2.u6015 from rfl, allE_node, arows6014, irow6016, arows6015]
  all_goals rfl

theorem atot6016 : totK PA10K2 A10K2.u6016 = [0, 0, 2127226231588, 7445592643796, 7138834549884, 1789994762904, 119348013684, 0, 0, 0] := by
  rw [show A10K2.u6016 = KTree.node A10K2.u6014 (nat_lit 102147478) (nat_lit 13918161593) (nat_lit 0) A10K2.u6015 from rfl, totK_node, atot6014, atot6015]
  decide +kernel

theorem arows6020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6020 = true := by
  rw [show A10K2.u6020 = KTree.node A10K2.u6018 (nat_lit 102236946) (nat_lit 3632944836) (nat_lit 0) A10K2.u6019 from rfl, allE_node, arows6018, irow6020, arows6019]
  all_goals rfl

theorem atot6020 : totK PA10K2 A10K2.u6020 = [835923233680, 3502586160559, 5036899655050, 4092203727073, 3490745008339, 1657917955844, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u6020 = KTree.node A10K2.u6018 (nat_lit 102236946) (nat_lit 3632944836) (nat_lit 0) A10K2.u6019 from rfl, totK_node, atot6018, atot6019]
  decide +kernel

theorem arows6023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6023 = true := by
  rw [show A10K2.u6023 = KTree.node A10K2.u6021 (nat_lit 102258701) (nat_lit 5823242822) (nat_lit 0) A10K2.u6022 from rfl, allE_node, arows6021, irow6023, arows6022]
  all_goals rfl

theorem atot6023 : totK PA10K2 A10K2.u6023 = [1341052302012, 5785105340971, 8024884856216, 3734633837135, 492056756612, 11814975521, 0, 0, 0, 0] := by
  rw [show A10K2.u6023 = KTree.node A10K2.u6021 (nat_lit 102258701) (nat_lit 5823242822) (nat_lit 0) A10K2.u6022 from rfl, totK_node, atot6021, atot6022]
  decide +kernel

theorem arows6028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6028 = true := by
  rw [show A10K2.u6028 = KTree.node A10K2.u6026 (nat_lit 102269395) (nat_lit 5519612769) (nat_lit 0) A10K2.u6027 from rfl, allE_node, arows6026, irow6028, arows6027]
  all_goals rfl

theorem atot6028 : totK PA10K2 A10K2.u6028 = [0, 1684942772791, 6591616438696, 7899954926119, 3062314719844, 453159263815, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u6028 = KTree.node A10K2.u6026 (nat_lit 102269395) (nat_lit 5519612769) (nat_lit 0) A10K2.u6027 from rfl, totK_node, atot6026, atot6027]
  decide +kernel

theorem arows6031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6031 = true := by
  rw [show A10K2.u6031 = KTree.node A10K2.u6029 (nat_lit 102289843) (nat_lit 5566106839) (nat_lit 0) A10K2.u6030 from rfl, allE_node, arows6029, irow6031, arows6030]
  all_goals rfl

theorem atot6031 : totK PA10K2 A10K2.u6031 = [0, 1338430235358, 5805352849662, 7983890364781, 3577838567726, 449025712068, 10957026886, 0, 0, 0] := by
  rw [show A10K2.u6031 = KTree.node A10K2.u6029 (nat_lit 102289843) (nat_lit 5566106839) (nat_lit 0) A10K2.u6030 from rfl, totK_node, atot6029, atot6030]
  decide +kernel

theorem arows6035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6035 = true := by
  rw [show A10K2.u6035 = KTree.node A10K2.u6033 (nat_lit 102315504) (nat_lit 11272360003) (nat_lit 0) A10K2.u6034 from rfl, allE_node, arows6033, irow6035, arows6034]
  all_goals rfl

theorem atot6035 : totK PA10K2 A10K2.u6035 = [1379420541293, 5711736010146, 7909206561837, 4241212480069, 901251688132, 69443663126, 0, 0, 0, 0] := by
  rw [show A10K2.u6035 = KTree.node A10K2.u6033 (nat_lit 102315504) (nat_lit 11272360003) (nat_lit 0) A10K2.u6034 from rfl, totK_node, atot6033, atot6034]
  decide +kernel

theorem arows6038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6038 = true := by
  rw [show A10K2.u6038 = KTree.node A10K2.u6036 (nat_lit 102334134) (nat_lit 16480875036) (nat_lit 0) A10K2.u6037 from rfl, allE_node, arows6036, irow6038, arows6037]
  all_goals rfl

theorem atot6038 : totK PA10K2 A10K2.u6038 = [227315038789, 2562800331274, 7440308090652, 7553829062044, 2345250137185, 157256452208, 0, 0, 0, 0] := by
  rw [show A10K2.u6038 = KTree.node A10K2.u6036 (nat_lit 102334134) (nat_lit 16480875036) (nat_lit 0) A10K2.u6037 from rfl, totK_node, atot6036, atot6037]
  decide +kernel

theorem arows6044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6044 = true := by
  rw [show A10K2.u6044 = KTree.node A10K2.u6042 (nat_lit 102362227) (nat_lit 6142457282) (nat_lit 0) A10K2.u6043 from rfl, allE_node, arows6042, irow6044, arows6043]
  all_goals rfl

theorem atot6044 : totK PA10K2 A10K2.u6044 = [777824669607, 3511914195007, 6221986694852, 5935043043181, 2942627388434, 566545006357, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6044 = KTree.node A10K2.u6042 (nat_lit 102362227) (nat_lit 6142457282) (nat_lit 0) A10K2.u6043 from rfl, totK_node, atot6042, atot6043]
  decide +kernel

theorem arows6047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6047 = true := by
  rw [show A10K2.u6047 = KTree.node A10K2.u6045 (nat_lit 102442928) (nat_lit 12008804521) (nat_lit 0) A10K2.u6046 from rfl, allE_node, arows6045, irow6047, arows6046]
  all_goals rfl

theorem atot6047 : totK PA10K2 A10K2.u6047 = [795116225951, 4413617083744, 8189249282103, 5448709279598, 1073289738370, 55614638191, 0, 0, 0, 0] := by
  rw [show A10K2.u6047 = KTree.node A10K2.u6045 (nat_lit 102442928) (nat_lit 12008804521) (nat_lit 0) A10K2.u6046 from rfl, totK_node, atot6045, atot6046]
  decide +kernel

theorem arows6051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6051 = true := by
  rw [show A10K2.u6051 = KTree.node A10K2.u6049 (nat_lit 102461943) (nat_lit 14886314268) (nat_lit 0) A10K2.u6050 from rfl, allE_node, arows6049, irow6051, arows6050]
  all_goals rfl

theorem atot6051 : totK PA10K2 A10K2.u6051 = [773825466003, 4153769849999, 7787533407011, 5775677656455, 1436432920940, 88459438038, 0, 0, 0, 0] := by
  rw [show A10K2.u6051 = KTree.node A10K2.u6049 (nat_lit 102461943) (nat_lit 14886314268) (nat_lit 0) A10K2.u6050 from rfl, totK_node, atot6049, atot6050]
  decide +kernel

theorem arows6054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6054 = true := by
  rw [show A10K2.u6054 = KTree.node A10K2.u6052 (nat_lit 102473153) (nat_lit 9707955790) (nat_lit 0) A10K2.u6053 from rfl, allE_node, arows6052, irow6054, arows6053]
  all_goals rfl

theorem atot6054 : totK PA10K2 A10K2.u6054 = [0, 1161156311007, 5413523744084, 8286126582598, 4404641046922, 636146644057, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u6054 = KTree.node A10K2.u6052 (nat_lit 102473153) (nat_lit 9707955790) (nat_lit 0) A10K2.u6053 from rfl, totK_node, atot6052, atot6053]
  decide +kernel

theorem arows6059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6059 = true := by
  rw [show A10K2.u6059 = KTree.node A10K2.u6057 (nat_lit 102493942) (nat_lit 16216547693) (nat_lit 0) A10K2.u6058 from rfl, allE_node, arows6057, irow6059, arows6058]
  all_goals rfl

theorem atot6059 : totK PA10K2 A10K2.u6059 = [0, 1088986660115, 4900616406191, 7811998708442, 5010021764275, 1049395328134, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u6059 = KTree.node A10K2.u6057 (nat_lit 102493942) (nat_lit 16216547693) (nat_lit 0) A10K2.u6058 from rfl, totK_node, atot6057, atot6058]
  decide +kernel

theorem arows6062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6062 = true := by
  rw [show A10K2.u6062 = KTree.node A10K2.u6060 (nat_lit 102503168) (nat_lit 14777115699) (nat_lit 0) A10K2.u6061 from rfl, allE_node, arows6060, irow6062, arows6061]
  all_goals rfl

theorem atot6062 : totK PA10K2 A10K2.u6062 = [0, 1149209988452, 5356258325654, 7878410340372, 3987609273558, 665330628097, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u6062 = KTree.node A10K2.u6060 (nat_lit 102503168) (nat_lit 14777115699) (nat_lit 0) A10K2.u6061 from rfl, totK_node, atot6060, atot6061]
  decide +kernel

theorem arows6066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6066 = true := by
  rw [show A10K2.u6066 = KTree.node A10K2.u6064 (nat_lit 102526419) (nat_lit 9928233936) (nat_lit 0) A10K2.u6065 from rfl, allE_node, arows6064, irow6066, arows6065]
  all_goals rfl

theorem atot6066 : totK PA10K2 A10K2.u6066 = [0, 820549055654, 4332771023662, 7970301468175, 5585022463978, 1251595678057, 68056836726, 0, 0, 0] := by
  rw [show A10K2.u6066 = KTree.node A10K2.u6064 (nat_lit 102526419) (nat_lit 9928233936) (nat_lit 0) A10K2.u6065 from rfl, totK_node, atot6064, atot6065]
  decide +kernel

theorem arows6069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6069 = true := by
  rw [show A10K2.u6069 = KTree.node A10K2.u6067 (nat_lit 102535692) (nat_lit 10904213204) (nat_lit 0) A10K2.u6068 from rfl, allE_node, arows6067, irow6069, arows6068]
  all_goals rfl

theorem atot6069 : totK PA10K2 A10K2.u6069 = [0, 0, 1578991826180, 6443644864604, 7748381896233, 2907499278941, 339835185838, 7007974415, 0, 0] := by
  rw [show A10K2.u6069 = KTree.node A10K2.u6067 (nat_lit 102535692) (nat_lit 10904213204) (nat_lit 0) A10K2.u6068 from rfl, totK_node, atot6067, atot6068]
  decide +kernel

theorem arows6076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6076 = true := by
  rw [show A10K2.u6076 = KTree.node A10K2.u6074 (nat_lit 102574323) (nat_lit 10208573370) (nat_lit 0) A10K2.u6075 from rfl, allE_node, arows6074, irow6076, arows6075]
  all_goals rfl

theorem atot6076 : totK PA10K2 A10K2.u6076 = [0, 779329081182, 4118667872143, 7690203341335, 5911631385660, 1554613275344, 100096519661, 0, 0, 0] := by
  rw [show A10K2.u6076 = KTree.node A10K2.u6074 (nat_lit 102574323) (nat_lit 10208573370) (nat_lit 0) A10K2.u6075 from rfl, totK_node, atot6074, atot6075]
  decide +kernel

theorem arows6079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6079 = true := by
  rw [show A10K2.u6079 = KTree.node A10K2.u6077 (nat_lit 102593030) (nat_lit 14956523810) (nat_lit 0) A10K2.u6078 from rfl, allE_node, arows6077, irow6079, arows6078]
  all_goals rfl

theorem atot6079 : totK PA10K2 A10K2.u6079 = [0, 825408880158, 4284015462169, 7868265194684, 5876901243664, 1471886471559, 88420430393, 0, 0, 0] := by
  rw [show A10K2.u6079 = KTree.node A10K2.u6077 (nat_lit 102593030) (nat_lit 14956523810) (nat_lit 0) A10K2.u6078 from rfl, totK_node, atot6077, atot6078]
  decide +kernel

theorem arows6083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6083 = true := by
  rw [show A10K2.u6083 = KTree.node A10K2.u6081 (nat_lit 102621573) (nat_lit 3730872056) (nat_lit 0) A10K2.u6082 from rfl, allE_node, arows6081, irow6083, arows6082]
  all_goals rfl

theorem atot6083 : totK PA10K2 A10K2.u6083 = [0, 300827602965, 2174091199157, 6258938438309, 7674842579011, 3269457535166, 378560991438, 7151180950, 0, 0] := by
  rw [show A10K2.u6083 = KTree.node A10K2.u6081 (nat_lit 102621573) (nat_lit 3730872056) (nat_lit 0) A10K2.u6082 from rfl, totK_node, atot6081, atot6082]
  decide +kernel

theorem arows6086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6086 = true := by
  rw [show A10K2.u6086 = KTree.node A10K2.u6084 (nat_lit 102702125) (nat_lit 2832086882) (nat_lit 0) A10K2.u6085 from rfl, allE_node, arows6084, irow6086, arows6085]
  all_goals rfl

theorem atot6086 : totK PA10K2 A10K2.u6086 = [0, 1162379276050, 5477394321274, 8351838261861, 4333342873514, 602489571319, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u6086 = KTree.node A10K2.u6084 (nat_lit 102702125) (nat_lit 2832086882) (nat_lit 0) A10K2.u6085 from rfl, totK_node, atot6084, atot6085]
  decide +kernel

theorem arows6091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6091 = true := by
  rw [show A10K2.u6091 = KTree.node A10K2.u6089 (nat_lit 102722781) (nat_lit 4740362911) (nat_lit 0) A10K2.u6090 from rfl, allE_node, arows6089, irow6091, arows6090]
  all_goals rfl

theorem atot6091 : totK PA10K2 A10K2.u6091 = [0, 882069215384, 4521349130461, 8081445800603, 5533562029103, 1059232179516, 31765231841, 0, 0, 0] := by
  rw [show A10K2.u6091 = KTree.node A10K2.u6089 (nat_lit 102722781) (nat_lit 4740362911) (nat_lit 0) A10K2.u6090 from rfl, totK_node, atot6089, atot6090]
  decide +kernel

theorem arows6094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6094 = true := by
  rw [show A10K2.u6094 = KTree.node A10K2.u6092 (nat_lit 102732229) (nat_lit 4174561116) (nat_lit 0) A10K2.u6093 from rfl, allE_node, arows6092, irow6094, arows6093]
  all_goals rfl

theorem atot6094 : totK PA10K2 A10K2.u6094 = [0, 0, 1458406702331, 6203684984584, 8341748484766, 3477076626942, 352924551886, 6318667960, 0, 0] := by
  rw [show A10K2.u6094 = KTree.node A10K2.u6092 (nat_lit 102732229) (nat_lit 4174561116) (nat_lit 0) A10K2.u6093 from rfl, totK_node, atot6092, atot6093]
  decide +kernel

theorem arows6098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6098 = true := by
  rw [show A10K2.u6098 = KTree.node A10K2.u6096 (nat_lit 102754227) (nat_lit 9774356499) (nat_lit 0) A10K2.u6097 from rfl, allE_node, arows6096, irow6098, arows6097]
  all_goals rfl

theorem atot6098 : totK PA10K2 A10K2.u6098 = [0, 0, 877185805802, 4757115901679, 8319766363078, 4983681324302, 746464252797, 18571798697, 0, 0] := by
  rw [show A10K2.u6098 = KTree.node A10K2.u6096 (nat_lit 102754227) (nat_lit 9774356499) (nat_lit 0) A10K2.u6097 from rfl, totK_node, atot6096, atot6097]
  decide +kernel

theorem arows6101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6101 = true := by
  rw [show A10K2.u6101 = KTree.node A10K2.u6099 (nat_lit 102764219) (nat_lit 6191947208) (nat_lit 0) A10K2.u6100 from rfl, allE_node, arows6099, irow6101, arows6100]
  all_goals rfl

theorem atot6101 : totK PA10K2 A10K2.u6101 = [0, 1163774037120, 4933866673997, 7021926081657, 4104386291880, 1606663702408, 532049653287, 48886019071, 0, 0] := by
  rw [show A10K2.u6101 = KTree.node A10K2.u6099 (nat_lit 102764219) (nat_lit 6191947208) (nat_lit 0) A10K2.u6100 from rfl, totK_node, atot6099, atot6100]
  decide +kernel

theorem arows6107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6107 = true := by
  rw [show A10K2.u6107 = KTree.node A10K2.u6105 (nat_lit 102783841) (nat_lit 8294315357) (nat_lit 0) A10K2.u6106 from rfl, allE_node, arows6105, irow6107, arows6106]
  all_goals rfl

theorem atot6107 : totK PA10K2 A10K2.u6107 = [0, 1175274676060, 5462948031009, 8108703647420, 3830425768734, 429385729647, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6107 = KTree.node A10K2.u6105 (nat_lit 102783841) (nat_lit 8294315357) (nat_lit 0) A10K2.u6106 from rfl, totK_node, atot6105, atot6106]
  decide +kernel

theorem arows6110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6110 = true := by
  rw [show A10K2.u6110 = KTree.node A10K2.u6108 (nat_lit 102795549) (nat_lit 6338507445) (nat_lit 0) A10K2.u6109 from rfl, allE_node, arows6108, irow6110, arows6109]
  all_goals rfl

theorem atot6110 : totK PA10K2 A10K2.u6110 = [0, 0, 1351092223342, 5792379058299, 7909594626037, 3643175882855, 596130918297, 30650496230, 0, 0] := by
  rw [show A10K2.u6110 = KTree.node A10K2.u6108 (nat_lit 102795549) (nat_lit 6338507445) (nat_lit 0) A10K2.u6109 from rfl, totK_node, atot6108, atot6109]
  decide +kernel

theorem arows6114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6114 = true := by
  rw [show A10K2.u6114 = KTree.node A10K2.u6112 (nat_lit 102815044) (nat_lit 12578999037) (nat_lit 0) A10K2.u6113 from rfl, allE_node, arows6112, irow6114, arows6113]
  all_goals rfl

theorem atot6114 : totK PA10K2 A10K2.u6114 = [0, 0, 1463781092346, 6191093499579, 7994092581169, 2977987048400, 289483909723, 5546304973, 0, 0] := by
  rw [show A10K2.u6114 = KTree.node A10K2.u6112 (nat_lit 102815044) (nat_lit 12578999037) (nat_lit 0) A10K2.u6113 from rfl, totK_node, atot6112, atot6113]
  decide +kernel

theorem arows6117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6117 = true := by
  rw [show A10K2.u6117 = KTree.node A10K2.u6115 (nat_lit 102896121) (nat_lit 6214476949) (nat_lit 0) A10K2.u6116 from rfl, allE_node, arows6115, irow6117, arows6116]
  all_goals rfl

theorem atot6117 : totK PA10K2 A10K2.u6117 = [0, 1088716171950, 4912622954104, 7629077540416, 4512160794133, 976957873906, 71820615639, 0, 0, 0] := by
  rw [show A10K2.u6117 = KTree.node A10K2.u6115 (nat_lit 102896121) (nat_lit 6214476949) (nat_lit 0) A10K2.u6116 from rfl, totK_node, atot6115, atot6116]
  decide +kernel

theorem arows6122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6122 = true := by
  rw [show A10K2.u6122 = KTree.node A10K2.u6120 (nat_lit 102914055) (nat_lit 10034485572) (nat_lit 0) A10K2.u6121 from rfl, allE_node, arows6120, irow6122, arows6121]
  all_goals rfl

theorem atot6122 : totK PA10K2 A10K2.u6122 = [0, 701069329253, 4155905548017, 7821355942636, 5214056246664, 1020311960730, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u6122 = KTree.node A10K2.u6120 (nat_lit 102914055) (nat_lit 10034485572) (nat_lit 0) A10K2.u6121 from rfl, totK_node, atot6120, atot6121]
  decide +kernel

theorem arows6125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6125 = true := by
  rw [show A10K2.u6125 = KTree.node A10K2.u6123 (nat_lit 102943572) (nat_lit 12912737647) (nat_lit 0) A10K2.u6124 from rfl, allE_node, arows6123, irow6125, arows6124]
  all_goals rfl

theorem atot6125 : totK PA10K2 A10K2.u6125 = [0, 617084332288, 3037325273130, 6381213013604, 6342009549159, 2190652114693, 230526887580, 5976421810, 0, 0] := by
  rw [show A10K2.u6125 = KTree.node A10K2.u6123 (nat_lit 102943572) (nat_lit 12912737647) (nat_lit 0) A10K2.u6124 from rfl, totK_node, atot6123, atot6124]
  decide +kernel

theorem arows6129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6129 = true := by
  rw [show A10K2.u6129 = KTree.node A10K2.u6127 (nat_lit 102966512) (nat_lit 9606773775) (nat_lit 0) A10K2.u6128 from rfl, allE_node, arows6127, irow6129, arows6128]
  all_goals rfl

theorem atot6129 : totK PA10K2 A10K2.u6129 = [0, 993745867467, 4978901026828, 8288899307171, 5028097258535, 903493559367, 38191721423, 0, 0, 0] := by
  rw [show A10K2.u6129 = KTree.node A10K2.u6127 (nat_lit 102966512) (nat_lit 9606773775) (nat_lit 0) A10K2.u6128 from rfl, totK_node, atot6127, atot6128]
  decide +kernel

theorem arows6132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6132 = true := by
  rw [show A10K2.u6132 = KTree.node A10K2.u6130 (nat_lit 102986999) (nat_lit 14492218206) (nat_lit 0) A10K2.u6131 from rfl, allE_node, arows6130, irow6132, arows6131]
  all_goals rfl

theorem atot6132 : totK PA10K2 A10K2.u6132 = [0, 557707638591, 3609826938883, 7802846832705, 6293433363248, 1584211678178, 88252797147, 0, 0, 0] := by
  rw [show A10K2.u6132 = KTree.node A10K2.u6130 (nat_lit 102986999) (nat_lit 14492218206) (nat_lit 0) A10K2.u6131 from rfl, totK_node, atot6130, atot6131]
  decide +kernel

theorem arows6144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6144 = true := by
  rw [show A10K2.u6144 = KTree.node A10K2.u6142 (nat_lit 102999728) (nat_lit 9594373260) (nat_lit 0) A10K2.u6143 from rfl, allE_node, arows6142, irow6144, arows6143]
  all_goals rfl

theorem atot6144 : totK PA10K2 A10K2.u6144 = [0, 0, 1573834415630, 6301822587363, 8220503396831, 3550194152050, 394695398785, 6904928264, 0, 0] := by
  rw [show A10K2.u6144 = KTree.node A10K2.u6142 (nat_lit 102999728) (nat_lit 9594373260) (nat_lit 0) A10K2.u6143 from rfl, totK_node, atot6142, atot6143]
  decide +kernel

theorem arows6147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6147 = true := by
  rw [show A10K2.u6147 = KTree.node A10K2.u6145 (nat_lit 103022985) (nat_lit 9623824707) (nat_lit 0) A10K2.u6146 from rfl, allE_node, arows6145, irow6147, arows6146]
  all_goals rfl

theorem atot6147 : totK PA10K2 A10K2.u6147 = [0, 0, 946581566776, 4885328551948, 8021882493449, 4779593494694, 944598276076, 54641311191, 0, 0] := by
  rw [show A10K2.u6147 = KTree.node A10K2.u6145 (nat_lit 103022985) (nat_lit 9623824707) (nat_lit 0) A10K2.u6146 from rfl, totK_node, atot6145, atot6146]
  decide +kernel

theorem arows6151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6151 = true := by
  rw [show A10K2.u6151 = KTree.node A10K2.u6149 (nat_lit 103041294) (nat_lit 8531122299) (nat_lit 0) A10K2.u6150 from rfl, allE_node, arows6149, irow6151, arows6150]
  all_goals rfl

theorem atot6151 : totK PA10K2 A10K2.u6151 = [0, 0, 1154209931150, 5131285130835, 7689771883626, 3916931106149, 576161933213, 16465930986, 0, 0] := by
  rw [show A10K2.u6151 = KTree.node A10K2.u6149 (nat_lit 103041294) (nat_lit 8531122299) (nat_lit 0) A10K2.u6150 from rfl, totK_node, atot6149, atot6150]
  decide +kernel

theorem arows6154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6154 = true := by
  rw [show A10K2.u6154 = KTree.node A10K2.u6152 (nat_lit 103055351) (nat_lit 14280407222) (nat_lit 0) A10K2.u6153 from rfl, allE_node, arows6152, irow6154, arows6153]
  all_goals rfl

theorem atot6154 : totK PA10K2 A10K2.u6154 = [0, 0, 305229480561, 2929409848662, 7497093220382, 6711105611218, 1870288480922, 127724721476, 0, 0] := by
  rw [show A10K2.u6154 = KTree.node A10K2.u6152 (nat_lit 103055351) (nat_lit 14280407222) (nat_lit 0) A10K2.u6153 from rfl, totK_node, atot6152, atot6153]
  decide +kernel

theorem arows6159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6159 = true := by
  rw [show A10K2.u6159 = KTree.node A10K2.u6157 (nat_lit 103073938) (nat_lit 9561354774) (nat_lit 0) A10K2.u6158 from rfl, allE_node, arows6157, irow6159, arows6158]
  all_goals rfl

theorem atot6159 : totK PA10K2 A10K2.u6159 = [0, 0, 0, 1144401313789, 5026225353103, 7356103249596, 3858045800666, 717296624071, 36134558889, 0] := by
  rw [show A10K2.u6159 = KTree.node A10K2.u6157 (nat_lit 103073938) (nat_lit 9561354774) (nat_lit 0) A10K2.u6158 from rfl, totK_node, atot6157, atot6158]
  decide +kernel

theorem arows6162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6162 = true := by
  rw [show A10K2.u6162 = KTree.node A10K2.u6160 (nat_lit 103157302) (nat_lit 16217637056) (nat_lit 0) A10K2.u6161 from rfl, allE_node, arows6160, irow6162, arows6161]
  all_goals rfl

theorem atot6162 : totK PA10K2 A10K2.u6162 = [0, 0, 1041409727014, 4896735504850, 7697780736557, 4514033484118, 950867417948, 59842360860, 0, 0] := by
  rw [show A10K2.u6162 = KTree.node A10K2.u6160 (nat_lit 103157302) (nat_lit 16217637056) (nat_lit 0) A10K2.u6161 from rfl, totK_node, atot6160, atot6161]
  decide +kernel

theorem arows6166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6166 = true := by
  rw [show A10K2.u6166 = KTree.node A10K2.u6164 (nat_lit 103174207) (nat_lit 10706951448) (nat_lit 0) A10K2.u6165 from rfl, allE_node, arows6164, irow6166, arows6165]
  all_goals rfl

theorem atot6166 : totK PA10K2 A10K2.u6166 = [0, 0, 740755107523, 4204329712041, 7850667795966, 4865573751396, 806689443625, 37643910412, 0, 0] := by
  rw [show A10K2.u6166 = KTree.node A10K2.u6164 (nat_lit 103174207) (nat_lit 10706951448) (nat_lit 0) A10K2.u6165 from rfl, totK_node, atot6164, atot6165]
  decide +kernel

theorem arows6169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6169 = true := by
  rw [show A10K2.u6169 = KTree.node A10K2.u6167 (nat_lit 103205085) (nat_lit 5503851969) (nat_lit 0) A10K2.u6168 from rfl, allE_node, arows6167, irow6169, arows6168]
  all_goals rfl

theorem atot6169 : totK PA10K2 A10K2.u6169 = [0, 0, 414273244854, 2576869521103, 6452625647880, 6661100097839, 2209546796777, 241207331249, 5676195732, 0] := by
  rw [show A10K2.u6169 = KTree.node A10K2.u6167 (nat_lit 103205085) (nat_lit 5503851969) (nat_lit 0) A10K2.u6168 from rfl, totK_node, atot6167, atot6168]
  decide +kernel

theorem arows6175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6175 = true := by
  rw [show A10K2.u6175 = KTree.node A10K2.u6173 (nat_lit 103228563) (nat_lit 11041069466) (nat_lit 0) A10K2.u6174 from rfl, allE_node, arows6173, irow6175, arows6174]
  all_goals rfl

theorem atot6175 : totK PA10K2 A10K2.u6175 = [0, 0, 1623326568078, 6397032416040, 8070083018113, 3483298831304, 444475457034, 20058242317, 0, 0] := by
  rw [show A10K2.u6175 = KTree.node A10K2.u6173 (nat_lit 103228563) (nat_lit 11041069466) (nat_lit 0) A10K2.u6174 from rfl, totK_node, atot6173, atot6174]
  decide +kernel

theorem arows6178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6178 = true := by
  rw [show A10K2.u6178 = KTree.node A10K2.u6176 (nat_lit 103809384) (nat_lit 9872716404) (nat_lit 0) A10K2.u6177 from rfl, allE_node, arows6176, irow6178, arows6177]
  all_goals rfl

theorem atot6178 : totK PA10K2 A10K2.u6178 = [0, 838792425063, 3497825470822, 5850133198524, 5662501178974, 3153838832359, 659593742267, 35503361870, 0, 0] := by
  rw [show A10K2.u6178 = KTree.node A10K2.u6176 (nat_lit 103809384) (nat_lit 9872716404) (nat_lit 0) A10K2.u6177 from rfl, totK_node, atot6176, atot6177]
  decide +kernel

theorem arows6182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6182 = true := by
  rw [show A10K2.u6182 = KTree.node A10K2.u6180 (nat_lit 103827618) (nat_lit 13527284891) (nat_lit 0) A10K2.u6181 from rfl, allE_node, arows6180, irow6182, arows6181]
  all_goals rfl

theorem atot6182 : totK PA10K2 A10K2.u6182 = [0, 1046709195442, 5003513637502, 7897259968164, 4348831636713, 667718584278, 17115393699, 0, 0, 0] := by
  rw [show A10K2.u6182 = KTree.node A10K2.u6180 (nat_lit 103827618) (nat_lit 13527284891) (nat_lit 0) A10K2.u6181 from rfl, totK_node, atot6180, atot6181]
  decide +kernel

theorem arows6185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6185 = true := by
  rw [show A10K2.u6185 = KTree.node A10K2.u6183 (nat_lit 103842188) (nat_lit 8936853582) (nat_lit 0) A10K2.u6184 from rfl, allE_node, arows6183, irow6185, arows6184]
  all_goals rfl

theorem atot6185 : totK PA10K2 A10K2.u6185 = [0, 295757175837, 2586536373166, 6875022555119, 6979689457370, 2560179802160, 409696789151, 25239774317, 0, 0] := by
  rw [show A10K2.u6185 = KTree.node A10K2.u6183 (nat_lit 103842188) (nat_lit 8936853582) (nat_lit 0) A10K2.u6184 from rfl, totK_node, atot6183, atot6184]
  decide +kernel

theorem arows6190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6190 = true := by
  rw [show A10K2.u6190 = KTree.node A10K2.u6188 (nat_lit 103860577) (nat_lit 8951841821) (nat_lit 0) A10K2.u6189 from rfl, allE_node, arows6188, irow6190, arows6189]
  all_goals rfl

theorem atot6190 : totK PA10K2 A10K2.u6190 = [0, 0, 1338397635507, 5719387754451, 7903617039036, 3546266551938, 457619074642, 10957026886, 0, 0] := by
  rw [show A10K2.u6190 = KTree.node A10K2.u6188 (nat_lit 103860577) (nat_lit 8951841821) (nat_lit 0) A10K2.u6189 from rfl, totK_node, atot6188, atot6189]
  decide +kernel

theorem arows6193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6193 = true := by
  rw [show A10K2.u6193 = KTree.node A10K2.u6191 (nat_lit 103944310) (nat_lit 14397856343) (nat_lit 0) A10K2.u6192 from rfl, allE_node, arows6191, irow6193, arows6192]
  all_goals rfl

theorem atot6193 : totK PA10K2 A10K2.u6193 = [0, 1286023981050, 5123937800902, 7395260064070, 4520011498546, 1018128997407, 60623532923, 0, 0, 0] := by
  rw [show A10K2.u6193 = KTree.node A10K2.u6191 (nat_lit 103944310) (nat_lit 14397856343) (nat_lit 0) A10K2.u6192 from rfl, totK_node, atot6191, atot6192]
  decide +kernel

theorem arows6197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6197 = true := by
  rw [show A10K2.u6197 = KTree.node A10K2.u6195 (nat_lit 103957722) (nat_lit 14151363605) (nat_lit 0) A10K2.u6196 from rfl, allE_node, arows6195, irow6197, arows6196]
  all_goals rfl

theorem atot6197 : totK PA10K2 A10K2.u6197 = [0, 859089464649, 4815363919097, 8087357702572, 4424968689380, 676735558031, 31333686660, 0, 0, 0] := by
  rw [show A10K2.u6197 = KTree.node A10K2.u6195 (nat_lit 103957722) (nat_lit 14151363605) (nat_lit 0) A10K2.u6196 from rfl, totK_node, atot6195, atot6196]
  decide +kernel

theorem arows6200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6200 = true := by
  rw [show A10K2.u6200 = KTree.node A10K2.u6198 (nat_lit 103982779) (nat_lit 6916277253) (nat_lit 0) A10K2.u6199 from rfl, allE_node, arows6198, irow6200, arows6199]
  all_goals rfl

theorem atot6200 : totK PA10K2 A10K2.u6200 = [0, 0, 2024870003248, 7287268204881, 7564488759211, 2027986403093, 127440919892, 0, 0, 0] := by
  rw [show A10K2.u6200 = KTree.node A10K2.u6198 (nat_lit 103982779) (nat_lit 6916277253) (nat_lit 0) A10K2.u6199 from rfl, totK_node, atot6198, atot6199]
  decide +kernel

theorem arows6207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6207 = true := by
  rw [show A10K2.u6207 = KTree.node A10K2.u6205 (nat_lit 104072072) (nat_lit 14261625976) (nat_lit 0) A10K2.u6206 from rfl, allE_node, arows6205, irow6207, arows6206]
  all_goals rfl

theorem atot6207 : totK PA10K2 A10K2.u6207 = [0, 0, 951366745023, 5047564894006, 8122084987125, 4038383345617, 686820996399, 31725663621, 0, 0] := by
  rw [show A10K2.u6207 = KTree.node A10K2.u6205 (nat_lit 104072072) (nat_lit 14261625976) (nat_lit 0) A10K2.u6206 from rfl, totK_node, atot6205, atot6206]
  decide +kernel

theorem arows6210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6210 = true := by
  rw [show A10K2.u6210 = KTree.node A10K2.u6208 (nat_lit 104091657) (nat_lit 9802626900) (nat_lit 0) A10K2.u6209 from rfl, allE_node, arows6208, irow6210, arows6209]
  all_goals rfl

theorem atot6210 : totK PA10K2 A10K2.u6210 = [0, 0, 1342466371279, 5699555595276, 7918385692585, 3666428765100, 464174672816, 11801668502, 0, 0] := by
  rw [show A10K2.u6210 = KTree.node A10K2.u6208 (nat_lit 104091657) (nat_lit 9802626900) (nat_lit 0) A10K2.u6209 from rfl, totK_node, atot6208, atot6209]
  decide +kernel

theorem arows6214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6214 = true := by
  rw [show A10K2.u6214 = KTree.node A10K2.u6212 (nat_lit 104205063) (nat_lit 7346397669) (nat_lit 0) A10K2.u6213 from rfl, allE_node, arows6212, irow6214, arows6213]
  all_goals rfl

theorem atot6214 : totK PA10K2 A10K2.u6214 = [0, 0, 1041395531197, 4957732709849, 7955164430460, 4478886933623, 760857624400, 36928231554, 0, 0] := by
  rw [show A10K2.u6214 = KTree.node A10K2.u6212 (nat_lit 104205063) (nat_lit 7346397669) (nat_lit 0) A10K2.u6213 from rfl, totK_node, atot6212, atot6213]
  decide +kernel

theorem arows6217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6217 = true := by
  rw [show A10K2.u6217 = KTree.node A10K2.u6215 (nat_lit 104219233) (nat_lit 9855019759) (nat_lit 0) A10K2.u6216 from rfl, allE_node, arows6215, irow6217, arows6216]
  all_goals rfl

theorem atot6217 : totK PA10K2 A10K2.u6217 = [0, 0, 1101110967193, 5596987842146, 8299903971094, 3392558710346, 365086112277, 6034215561, 0, 0] := by
  rw [show A10K2.u6217 = KTree.node A10K2.u6215 (nat_lit 104219233) (nat_lit 9855019759) (nat_lit 0) A10K2.u6216 from rfl, totK_node, atot6215, atot6216]
  decide +kernel

theorem arows6222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6222 = true := by
  rw [show A10K2.u6222 = KTree.node A10K2.u6220 (nat_lit 104245288) (nat_lit 11686520292) (nat_lit 0) A10K2.u6221 from rfl, allE_node, arows6220, irow6222, arows6221]
  all_goals rfl

theorem atot6222 : totK PA10K2 A10K2.u6222 = [0, 0, 0, 2226686635263, 7750933088937, 6877195580139, 1550377444541, 74461528785, 0, 0] := by
  rw [show A10K2.u6222 = KTree.node A10K2.u6220 (nat_lit 104245288) (nat_lit 11686520292) (nat_lit 0) A10K2.u6221 from rfl, totK_node, atot6220, atot6221]
  decide +kernel

theorem arows6225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6225 = true := by
  rw [show A10K2.u6225 = KTree.node A10K2.u6223 (nat_lit 104336210) (nat_lit 3951954165) (nat_lit 0) A10K2.u6224 from rfl, allE_node, arows6223, irow6225, arows6224]
  all_goals rfl

theorem atot6225 : totK PA10K2 A10K2.u6225 = [0, 835923233680, 3887850203196, 5999006961822, 4120618058770, 2580475721902, 1224462494268, 193255931756, 5976421810, 0] := by
  rw [show A10K2.u6225 = KTree.node A10K2.u6223 (nat_lit 104336210) (nat_lit 3951954165) (nat_lit 0) A10K2.u6224 from rfl, totK_node, atot6223, atot6224]
  decide +kernel

theorem arows6229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6229 = true := by
  rw [show A10K2.u6229 = KTree.node A10K2.u6227 (nat_lit 104358152) (nat_lit 14123762134) (nat_lit 0) A10K2.u6228 from rfl, allE_node, arows6227, irow6229, arows6228]
  all_goals rfl

theorem atot6229 : totK PA10K2 A10K2.u6229 = [0, 1341052302012, 5723078960174, 8008032074811, 3901619938032, 545099962580, 12829769818, 0, 0, 0] := by
  rw [show A10K2.u6229 = KTree.node A10K2.u6227 (nat_lit 104358152) (nat_lit 14123762134) (nat_lit 0) A10K2.u6228 from rfl, totK_node, atot6227, atot6228]
  decide +kernel

theorem arows6232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6232 = true := by
  rw [show A10K2.u6232 = KTree.node A10K2.u6230 (nat_lit 104368483) (nat_lit 7552416981) (nat_lit 0) A10K2.u6231 from rfl, allE_node, arows6230, irow6232, arows6231]
  all_goals rfl

theorem atot6232 : totK PA10K2 A10K2.u6232 = [0, 0, 1360020553270, 5845518600731, 7938523813794, 3664333007170, 606953888231, 30650496230, 0, 0] := by
  rw [show A10K2.u6232 = KTree.node A10K2.u6230 (nat_lit 104368483) (nat_lit 7552416981) (nat_lit 0) A10K2.u6231 from rfl, totK_node, atot6230, atot6231]
  decide +kernel

theorem arows6238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6238 = true := by
  rw [show A10K2.u6238 = KTree.node A10K2.u6236 (nat_lit 104392583) (nat_lit 14383425180) (nat_lit 0) A10K2.u6237 from rfl, allE_node, arows6236, irow6238, arows6237]
  all_goals rfl

theorem atot6238 : totK PA10K2 A10K2.u6238 = [0, 779827310996, 3903555179072, 7303742052056, 6021616130703, 1742414010357, 131981601157, 0, 0, 0] := by
  rw [show A10K2.u6238 = KTree.node A10K2.u6236 (nat_lit 104392583) (nat_lit 14383425180) (nat_lit 0) A10K2.u6237 from rfl, totK_node, atot6236, atot6237]
  decide +kernel

theorem arows6241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6241 = true := by
  rw [show A10K2.u6241 = KTree.node A10K2.u6239 (nat_lit 104424611) (nat_lit 10582390618) (nat_lit 0) A10K2.u6240 from rfl, allE_node, arows6239, irow6241, arows6240]
  all_goals rfl

theorem atot6241 : totK PA10K2 A10K2.u6241 = [0, 826908269086, 4622342251082, 8465512798614, 5497056168946, 981616369023, 38129137030, 0, 0, 0] := by
  rw [show A10K2.u6241 = KTree.node A10K2.u6239 (nat_lit 104424611) (nat_lit 10582390618) (nat_lit 0) A10K2.u6240 from rfl, totK_node, atot6239, atot6240]
  decide +kernel

theorem arows6245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6245 = true := by
  rw [show A10K2.u6245 = KTree.node A10K2.u6243 (nat_lit 104443321) (nat_lit 6509671036) (nat_lit 0) A10K2.u6244 from rfl, allE_node, arows6243, irow6245, arows6244]
  all_goals rfl

theorem atot6245 : totK PA10K2 A10K2.u6245 = [0, 0, 1602345549857, 6528102835179, 8244267711489, 3385281681248, 389395654550, 7380853412, 0, 0] := by
  rw [show A10K2.u6245 = KTree.node A10K2.u6243 (nat_lit 104443321) (nat_lit 6509671036) (nat_lit 0) A10K2.u6244 from rfl, totK_node, atot6243, atot6244]
  decide +kernel

theorem arows6248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6248 = true := by
  rw [show A10K2.u6248 = KTree.node A10K2.u6246 (nat_lit 104533139) (nat_lit 10546307130) (nat_lit 0) A10K2.u6247 from rfl, allE_node, arows6246, irow6248, arows6247]
  all_goals rfl

theorem atot6248 : totK PA10K2 A10K2.u6248 = [0, 1030662607010, 4521718843800, 7419157656116, 5294579863186, 1384115459419, 88528422609, 0, 0, 0] := by
  rw [show A10K2.u6248 = KTree.node A10K2.u6246 (nat_lit 104533139) (nat_lit 10546307130) (nat_lit 0) A10K2.u6247 from rfl, totK_node, atot6246, atot6247]
  decide +kernel

theorem arows6253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6253 = true := by
  rw [show A10K2.u6253 = KTree.node A10K2.u6251 (nat_lit 104545492) (nat_lit 10304146582) (nat_lit 0) A10K2.u6252 from rfl, allE_node, arows6251, irow6253, arows6252]
  all_goals rfl

theorem atot6253 : totK PA10K2 A10K2.u6253 = [0, 1316103754551, 5873433309404, 8397309619981, 4110703595692, 570255094398, 12692412833, 0, 0, 0] := by
  rw [show A10K2.u6253 = KTree.node A10K2.u6251 (nat_lit 104545492) (nat_lit 10304146582) (nat_lit 0) A10K2.u6252 from rfl, totK_node, atot6251, atot6252]
  decide +kernel

theorem arows6256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6256 = true := by
  rw [show A10K2.u6256 = KTree.node A10K2.u6254 (nat_lit 104563144) (nat_lit 14209543142) (nat_lit 0) A10K2.u6255 from rfl, allE_node, arows6254, irow6256, arows6255]
  all_goals rfl

theorem atot6256 : totK PA10K2 A10K2.u6256 = [0, 0, 1640768191346, 6527033953502, 8013147643275, 3184450458873, 362177420762, 6904928264, 0, 0] := by
  rw [show A10K2.u6256 = KTree.node A10K2.u6254 (nat_lit 104563144) (nat_lit 14209543142) (nat_lit 0) A10K2.u6255 from rfl, totK_node, atot6254, atot6255]
  decide +kernel

theorem arows6260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6260 = true := by
  rw [show A10K2.u6260 = KTree.node A10K2.u6258 (nat_lit 104576660) (nat_lit 11209870260) (nat_lit 0) A10K2.u6259 from rfl, allE_node, arows6258, irow6260, arows6259]
  all_goals rfl

theorem atot6260 : totK PA10K2 A10K2.u6260 = [0, 0, 1565199395711, 6404528283606, 8223656673350, 3551226181780, 373122106849, 6766355402, 0, 0] := by
  rw [show A10K2.u6260 = KTree.node A10K2.u6258 (nat_lit 104576660) (nat_lit 11209870260) (nat_lit 0) A10K2.u6259 from rfl, totK_node, atot6258, atot6259]
  decide +kernel

theorem arows6263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6263 = true := by
  rw [show A10K2.u6263 = KTree.node A10K2.u6261 (nat_lit 104595447) (nat_lit 14899910164) (nat_lit 0) A10K2.u6262 from rfl, allE_node, arows6261, irow6263, arows6262]
  all_goals rfl

theorem atot6263 : totK PA10K2 A10K2.u6263 = [872244600920, 3408362204235, 4004825828675, 2567703044211, 4062249790722, 3741235854200, 967700588216, 61110126106, 0, 0] := by
  rw [show A10K2.u6263 = KTree.node A10K2.u6261 (nat_lit 104595447) (nat_lit 14899910164) (nat_lit 0) A10K2.u6262 from rfl, totK_node, atot6261, atot6262]
  decide +kernel

theorem arows6271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6271 = true := by
  rw [show A10K2.u6271 = KTree.node A10K2.u6269 (nat_lit 105465623) (nat_lit 9673123763) (nat_lit 0) A10K2.u6270 from rfl, allE_node, arows6269, irow6271, arows6270]
  all_goals rfl

theorem atot6271 : totK PA10K2 A10K2.u6271 = [903465458956, 4503229938221, 7748252810723, 4774895870983, 872461304315, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u6271 = KTree.node A10K2.u6269 (nat_lit 105465623) (nat_lit 9673123763) (nat_lit 0) A10K2.u6270 from rfl, totK_node, atot6269, atot6270]
  decide +kernel

theorem arows6274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6274 = true := by
  rw [show A10K2.u6274 = KTree.node A10K2.u6272 (nat_lit 105477852) (nat_lit 8616036484) (nat_lit 0) A10K2.u6273 from rfl, allE_node, arows6272, irow6274, arows6273]
  all_goals rfl

theorem atot6274 : totK PA10K2 A10K2.u6274 = [568469117275, 3644584272707, 7720306109081, 6259915626230, 1585858279011, 95185527653, 0, 0, 0, 0] := by
  rw [show A10K2.u6274 = KTree.node A10K2.u6272 (nat_lit 105477852) (nat_lit 8616036484) (nat_lit 0) A10K2.u6273 from rfl, totK_node, atot6272, atot6273]
  decide +kernel

theorem arows6278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6278 = true := by
  rw [show A10K2.u6278 = KTree.node A10K2.u6276 (nat_lit 105496861) (nat_lit 6390285910) (nat_lit 0) A10K2.u6277 from rfl, allE_node, arows6276, irow6278, arows6277]
  all_goals rfl

theorem atot6278 : totK PA10K2 A10K2.u6278 = [0, 908304950511, 4831386534850, 7985062913664, 4294576087774, 681159747754, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6278 = KTree.node A10K2.u6276 (nat_lit 105496861) (nat_lit 6390285910) (nat_lit 0) A10K2.u6277 from rfl, totK_node, atot6276, atot6277]
  decide +kernel

theorem arows6281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6281 = true := by
  rw [show A10K2.u6281 = KTree.node A10K2.u6279 (nat_lit 105515155) (nat_lit 10670814160) (nat_lit 0) A10K2.u6280 from rfl, allE_node, arows6279, irow6281, arows6280]
  all_goals rfl

theorem atot6281 : totK PA10K2 A10K2.u6281 = [830637671679, 4062650118849, 6979123459797, 5344150112364, 1886367777640, 230428261234, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6281 = KTree.node A10K2.u6279 (nat_lit 105515155) (nat_lit 10670814160) (nat_lit 0) A10K2.u6280 from rfl, totK_node, atot6279, atot6280]
  decide +kernel

theorem arows6286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6286 = true := by
  rw [show A10K2.u6286 = KTree.node A10K2.u6284 (nat_lit 105529683) (nat_lit 9997548984) (nat_lit 0) A10K2.u6285 from rfl, allE_node, arows6284, irow6286, arows6285]
  all_goals rfl

theorem atot6286 : totK PA10K2 A10K2.u6286 = [962840194868, 4905676584784, 8003773238384, 4639696431255, 772508930128, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6286 = KTree.node A10K2.u6284 (nat_lit 105529683) (nat_lit 9997548984) (nat_lit 0) A10K2.u6285 from rfl, totK_node, atot6284, atot6285]
  decide +kernel

theorem arows6289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6289 = true := by
  rw [show A10K2.u6289 = KTree.node A10K2.u6287 (nat_lit 105556800) (nat_lit 11648125351) (nat_lit 0) A10K2.u6288 from rfl, allE_node, arows6287, irow6289, arows6288]
  all_goals rfl

theorem atot6289 : totK PA10K2 A10K2.u6289 = [0, 1922220795398, 7297677678214, 7669372836053, 2012591186113, 108676975043, 0, 0, 0, 0] := by
  rw [show A10K2.u6289 = KTree.node A10K2.u6287 (nat_lit 105556800) (nat_lit 11648125351) (nat_lit 0) A10K2.u6288 from rfl, totK_node, atot6287, atot6288]
  decide +kernel

theorem arows6293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6293 = true := by
  rw [show A10K2.u6293 = KTree.node A10K2.u6291 (nat_lit 105582597) (nat_lit 6183737542) (nat_lit 0) A10K2.u6292 from rfl, allE_node, arows6291, irow6293, arows6292]
  all_goals rfl

theorem atot6293 : totK PA10K2 A10K2.u6293 = [1324242768764, 5030821084359, 6783199215763, 4640616874173, 1775950081734, 278815988305, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6293 = KTree.node A10K2.u6291 (nat_lit 105582597) (nat_lit 6183737542) (nat_lit 0) A10K2.u6292 from rfl, totK_node, atot6291, atot6292]
  decide +kernel

theorem arows6296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6296 = true := by
  rw [show A10K2.u6296 = KTree.node A10K2.u6294 (nat_lit 105603655) (nat_lit 9934066887) (nat_lit 0) A10K2.u6295 from rfl, allE_node, arows6294, irow6296, arows6295]
  all_goals rfl

theorem atot6296 : totK PA10K2 A10K2.u6296 = [846194190982, 4678053526264, 8336317300563, 5179769757918, 939998658752, 38600540508, 0, 0, 0, 0] := by
  rw [show A10K2.u6296 = KTree.node A10K2.u6294 (nat_lit 105603655) (nat_lit 9934066887) (nat_lit 0) A10K2.u6295 from rfl, totK_node, atot6294, atot6295]
  decide +kernel

theorem arows6302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6302 = true := by
  rw [show A10K2.u6302 = KTree.node A10K2.u6300 (nat_lit 105615282) (nat_lit 13770425449) (nat_lit 0) A10K2.u6301 from rfl, allE_node, arows6300, irow6302, arows6301]
  all_goals rfl

theorem atot6302 : totK PA10K2 A10K2.u6302 = [0, 1674569903155, 6603289114312, 8167012952001, 3384807955820, 407522368913, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6302 = KTree.node A10K2.u6300 (nat_lit 105615282) (nat_lit 13770425449) (nat_lit 0) A10K2.u6301 from rfl, totK_node, atot6300, atot6301]
  decide +kernel

theorem arows6305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6305 = true := by
  rw [show A10K2.u6305 = KTree.node A10K2.u6303 (nat_lit 105637075) (nat_lit 10853699543) (nat_lit 0) A10K2.u6304 from rfl, allE_node, arows6303, irow6305, arows6304]
  all_goals rfl

theorem atot6305 : totK PA10K2 A10K2.u6305 = [0, 930022939094, 5007420332765, 8480874412732, 4897352873935, 698443592762, 13113983930, 0, 0, 0] := by
  rw [show A10K2.u6305 = KTree.node A10K2.u6303 (nat_lit 105637075) (nat_lit 10853699543) (nat_lit 0) A10K2.u6304 from rfl, totK_node, atot6303, atot6304]
  decide +kernel

theorem arows6309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6309 = true := by
  rw [show A10K2.u6309 = KTree.node A10K2.u6307 (nat_lit 105720902) (nat_lit 14531155286) (nat_lit 0) A10K2.u6308 from rfl, allE_node, arows6307, irow6309, arows6308]
  all_goals rfl

theorem atot6309 : totK PA10K2 A10K2.u6309 = [0, 869750410530, 4368454792483, 7637595478796, 5214264638146, 1253527178225, 86811916481, 0, 0, 0] := by
  rw [show A10K2.u6309 = KTree.node A10K2.u6307 (nat_lit 105720902) (nat_lit 14531155286) (nat_lit 0) A10K2.u6308 from rfl, totK_node, atot6307, atot6308]
  decide +kernel

theorem arows6312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6312 = true := by
  rw [show A10K2.u6312 = KTree.node A10K2.u6310 (nat_lit 105732254) (nat_lit 11821072633) (nat_lit 0) A10K2.u6311 from rfl, allE_node, arows6310, irow6312, arows6311]
  all_goals rfl

theorem atot6312 : totK PA10K2 A10K2.u6312 = [0, 1470347982880, 6067143013232, 7919176850116, 3296722000988, 335575580919, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6312 = KTree.node A10K2.u6310 (nat_lit 105732254) (nat_lit 11821072633) (nat_lit 0) A10K2.u6311 from rfl, totK_node, atot6310, atot6311]
  decide +kernel

theorem arows6317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6317 = true := by
  rw [show A10K2.u6317 = KTree.node A10K2.u6315 (nat_lit 105752362) (nat_lit 12526482812) (nat_lit 0) A10K2.u6316 from rfl, allE_node, arows6315, irow6317, arows6316]
  all_goals rfl

theorem atot6317 : totK PA10K2 A10K2.u6317 = [0, 0, 1642790249509, 6507299256813, 7773444736256, 3091000034607, 465065780367, 25565504801, 0, 0] := by
  rw [show A10K2.u6317 = KTree.node A10K2.u6315 (nat_lit 105752362) (nat_lit 12526482812) (nat_lit 0) A10K2.u6316 from rfl, totK_node, atot6315, atot6316]
  decide +kernel

theorem arows6320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6320 = true := by
  rw [show A10K2.u6320 = KTree.node A10K2.u6318 (nat_lit 105763155) (nat_lit 6457367252) (nat_lit 0) A10K2.u6319 from rfl, allE_node, arows6318, irow6320, arows6319]
  all_goals rfl

theorem atot6320 : totK PA10K2 A10K2.u6320 = [0, 0, 1460295047452, 5909557987776, 7678578223097, 3273140909040, 415744431308, 11138589073, 0, 0] := by
  rw [show A10K2.u6320 = KTree.node A10K2.u6318 (nat_lit 105763155) (nat_lit 6457367252) (nat_lit 0) A10K2.u6319 from rfl, totK_node, atot6318, atot6319]
  decide +kernel

theorem arows6324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6324 = true := by
  rw [show A10K2.u6324 = KTree.node A10K2.u6322 (nat_lit 105785668) (nat_lit 13016561887) (nat_lit 0) A10K2.u6323 from rfl, allE_node, arows6322, irow6324, arows6323]
  all_goals rfl

theorem atot6324 : totK PA10K2 A10K2.u6324 = [0, 1050022894405, 4873904568284, 7601767477919, 4617023306632, 1013830318367, 68505397644, 0, 0, 0] := by
  rw [show A10K2.u6324 = KTree.node A10K2.u6322 (nat_lit 105785668) (nat_lit 13016561887) (nat_lit 0) A10K2.u6323 from rfl, totK_node, atot6322, atot6323]
  decide +kernel

theorem arows6327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6327 = true := by
  rw [show A10K2.u6327 = KTree.node A10K2.u6325 (nat_lit 105796962) (nat_lit 12966212161) (nat_lit 0) A10K2.u6326 from rfl, allE_node, arows6325, irow6327, arows6326]
  all_goals rfl

theorem atot6327 : totK PA10K2 A10K2.u6327 = [0, 743454972142, 4262489363492, 7804155508945, 5039301042345, 921653274135, 38593611784, 0, 0, 0] := by
  rw [show A10K2.u6327 = KTree.node A10K2.u6325 (nat_lit 105796962) (nat_lit 12966212161) (nat_lit 0) A10K2.u6326 from rfl, totK_node, atot6325, atot6326]
  decide +kernel

theorem arows6334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6334 = true := by
  rw [show A10K2.u6334 = KTree.node A10K2.u6332 (nat_lit 105827072) (nat_lit 13829741916) (nat_lit 0) A10K2.u6333 from rfl, allE_node, arows6332, irow6334, arows6333]
  all_goals rfl

theorem atot6334 : totK PA10K2 A10K2.u6334 = [0, 511028321977, 2760810300561, 6477231384971, 6796542841367, 2367893763790, 258715959954, 6239673734, 0, 0] := by
  rw [show A10K2.u6334 = KTree.node A10K2.u6332 (nat_lit 105827072) (nat_lit 13829741916) (nat_lit 0) A10K2.u6333 from rfl, totK_node, atot6332, atot6333]
  decide +kernel

theorem arows6337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6337 = true := by
  rw [show A10K2.u6337 = KTree.node A10K2.u6335 (nat_lit 105852145) (nat_lit 5712052036) (nat_lit 0) A10K2.u6336 from rfl, allE_node, arows6335, irow6337, arows6336]
  all_goals rfl

theorem atot6337 : totK PA10K2 A10K2.u6337 = [0, 1042976881812, 4921084167522, 8039378769165, 4968705537539, 932099357156, 38293342501, 0, 0, 0] := by
  rw [show A10K2.u6337 = KTree.node A10K2.u6335 (nat_lit 105852145) (nat_lit 5712052036) (nat_lit 0) A10K2.u6336 from rfl, totK_node, atot6335, atot6336]
  decide +kernel

theorem arows6341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6341 = true := by
  rw [show A10K2.u6341 = KTree.node A10K2.u6339 (nat_lit 105870520) (nat_lit 10209778523) (nat_lit 0) A10K2.u6340 from rfl, allE_node, arows6339, irow6341, arows6340]
  all_goals rfl

theorem atot6341 : totK PA10K2 A10K2.u6341 = [506965099532, 2225373996241, 4931944127769, 6722779611693, 4480377379642, 1059038015215, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u6341 = KTree.node A10K2.u6339 (nat_lit 105870520) (nat_lit 10209778523) (nat_lit 0) A10K2.u6340 from rfl, totK_node, atot6339, atot6340]
  decide +kernel

theorem arows6344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6344 = true := by
  rw [show A10K2.u6344 = KTree.node A10K2.u6342 (nat_lit 105987120) (nat_lit 10716044264) (nat_lit 0) A10K2.u6343 from rfl, allE_node, arows6342, irow6344, arows6343]
  all_goals rfl

theorem atot6344 : totK PA10K2 A10K2.u6344 = [1085859315942, 5194823325533, 7921735388349, 4275880798751, 711859662176, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6344 = KTree.node A10K2.u6342 (nat_lit 105987120) (nat_lit 10716044264) (nat_lit 0) A10K2.u6343 from rfl, totK_node, atot6342, atot6343]
  decide +kernel

theorem arows6349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6349 = true := by
  rw [show A10K2.u6349 = KTree.node A10K2.u6347 (nat_lit 106000305) (nat_lit 8641625279) (nat_lit 0) A10K2.u6348 from rfl, allE_node, arows6347, irow6349, arows6348]
  all_goals rfl

theorem atot6349 : totK PA10K2 A10K2.u6349 = [595155796918, 3811453437362, 7913756096850, 6002662943330, 1471125771922, 88831573858, 0, 0, 0, 0] := by
  rw [show A10K2.u6349 = KTree.node A10K2.u6347 (nat_lit 106000305) (nat_lit 8641625279) (nat_lit 0) A10K2.u6348 from rfl, totK_node, atot6347, atot6348]
  decide +kernel

theorem arows6352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6352 = true := by
  rw [show A10K2.u6352 = KTree.node A10K2.u6350 (nat_lit 106019620) (nat_lit 14079638854) (nat_lit 0) A10K2.u6351 from rfl, allE_node, arows6350, irow6352, arows6351]
  all_goals rfl

theorem atot6352 : totK PA10K2 A10K2.u6352 = [0, 1126073477738, 5408780515981, 7959922511231, 3898587100303, 627584611602, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6352 = KTree.node A10K2.u6350 (nat_lit 106019620) (nat_lit 14079638854) (nat_lit 0) A10K2.u6351 from rfl, totK_node, atot6350, atot6351]
  decide +kernel

theorem arows6356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6356 = true := by
  rw [show A10K2.u6356 = KTree.node A10K2.u6354 (nat_lit 106033114) (nat_lit 13282809488) (nat_lit 0) A10K2.u6355 from rfl, allE_node, arows6354, irow6356, arows6355]
  all_goals rfl

theorem atot6356 : totK PA10K2 A10K2.u6356 = [561156172308, 3190346907011, 6540386484939, 6220328812989, 2559262028005, 303249337847, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6356 = KTree.node A10K2.u6354 (nat_lit 106033114) (nat_lit 13282809488) (nat_lit 0) A10K2.u6355 from rfl, totK_node, atot6354, atot6355]
  decide +kernel

theorem arows6359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6359 = true := by
  rw [show A10K2.u6359 = KTree.node A10K2.u6357 (nat_lit 106050967) (nat_lit 13276784823) (nat_lit 0) A10K2.u6358 from rfl, allE_node, arows6357, irow6359, arows6358]
  all_goals rfl

theorem atot6359 : totK PA10K2 A10K2.u6359 = [1281221941488, 5271461868128, 7514188715178, 4317887989897, 818486144201, 37229241746, 0, 0, 0, 0] := by
  rw [show A10K2.u6359 = KTree.node A10K2.u6357 (nat_lit 106050967) (nat_lit 13276784823) (nat_lit 0) A10K2.u6358 from rfl, totK_node, atot6357, atot6358]
  decide +kernel

theorem arows6365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6365 = true := by
  rw [show A10K2.u6365 = KTree.node A10K2.u6363 (nat_lit 106070135) (nat_lit 12570251952) (nat_lit 0) A10K2.u6364 from rfl, allE_node, arows6363, irow6365, arows6364]
  all_goals rfl

theorem atot6365 : totK PA10K2 A10K2.u6365 = [306750524226, 3232629337817, 7982734240696, 6149520209870, 1314257672330, 64458694438, 0, 0, 0, 0] := by
  rw [show A10K2.u6365 = KTree.node A10K2.u6363 (nat_lit 106070135) (nat_lit 12570251952) (nat_lit 0) A10K2.u6364 from rfl, totK_node, atot6363, atot6364]
  decide +kernel

theorem arows6368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6368 = true := by
  rw [show A10K2.u6368 = KTree.node A10K2.u6366 (nat_lit 106089143) (nat_lit 7219794565) (nat_lit 0) A10K2.u6367 from rfl, allE_node, arows6366, irow6368, arows6367]
  all_goals rfl

theorem atot6368 : totK PA10K2 A10K2.u6368 = [0, 1482552001290, 6132531869780, 7918150241040, 3049983502753, 355760088271, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6368 = KTree.node A10K2.u6366 (nat_lit 106089143) (nat_lit 7219794565) (nat_lit 0) A10K2.u6367 from rfl, totK_node, atot6366, atot6367]
  decide +kernel

theorem arows6372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6372 = true := by
  rw [show A10K2.u6372 = KTree.node A10K2.u6370 (nat_lit 106249068) (nat_lit 11448348864) (nat_lit 0) A10K2.u6371 from rfl, allE_node, arows6370, irow6372, arows6371]
  all_goals rfl

theorem atot6372 : totK PA10K2 A10K2.u6372 = [0, 1113399153764, 5220377992666, 7909849060446, 4181919702783, 675797524624, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u6372 = KTree.node A10K2.u6370 (nat_lit 106249068) (nat_lit 11448348864) (nat_lit 0) A10K2.u6371 from rfl, totK_node, atot6370, atot6371]
  decide +kernel

theorem arows6375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6375 = true := by
  rw [show A10K2.u6375 = KTree.node A10K2.u6373 (nat_lit 106262448) (nat_lit 13814147849) (nat_lit 0) A10K2.u6374 from rfl, allE_node, arows6373, irow6375, arows6374]
  all_goals rfl

theorem atot6375 : totK PA10K2 A10K2.u6375 = [0, 1155701875031, 5396209140640, 8244871633933, 4339045428675, 623652464235, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u6375 = KTree.node A10K2.u6373 (nat_lit 106262448) (nat_lit 13814147849) (nat_lit 0) A10K2.u6374 from rfl, totK_node, atot6373, atot6374]
  decide +kernel

theorem arows6380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6380 = true := by
  rw [show A10K2.u6380 = KTree.node A10K2.u6378 (nat_lit 106309992) (nat_lit 9482828573) (nat_lit 0) A10K2.u6379 from rfl, allE_node, arows6378, irow6380, arows6379]
  all_goals rfl

theorem atot6380 : totK PA10K2 A10K2.u6380 = [0, 868493731907, 4374834838493, 7730518152084, 4958855915247, 959330633971, 61078328232, 0, 0, 0] := by
  rw [show A10K2.u6380 = KTree.node A10K2.u6378 (nat_lit 106309992) (nat_lit 9482828573) (nat_lit 0) A10K2.u6379 from rfl, totK_node, atot6378, atot6379]
  decide +kernel

theorem arows6383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6383 = true := by
  rw [show A10K2.u6383 = KTree.node A10K2.u6381 (nat_lit 106321197) (nat_lit 6613700219) (nat_lit 0) A10K2.u6382 from rfl, allE_node, arows6381, irow6383, arows6382]
  all_goals rfl

theorem atot6383 : totK PA10K2 A10K2.u6383 = [0, 717479327981, 4343262060708, 7969621656553, 4856863938619, 859995459806, 37547833973, 0, 0, 0] := by
  rw [show A10K2.u6383 = KTree.node A10K2.u6381 (nat_lit 106321197) (nat_lit 6613700219) (nat_lit 0) A10K2.u6382 from rfl, totK_node, atot6381, atot6382]
  decide +kernel

theorem arows6387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6387 = true := by
  rw [show A10K2.u6387 = KTree.node A10K2.u6385 (nat_lit 106350354) (nat_lit 14885023895) (nat_lit 0) A10K2.u6386 from rfl, allE_node, arows6385, irow6387, arows6386]
  all_goals rfl

theorem atot6387 : totK PA10K2 A10K2.u6387 = [303494667383, 698722476234, 1646197752743, 5677966011088, 7067946825435, 2712170647945, 347414729890, 6354482628, 0, 0] := by
  rw [show A10K2.u6387 = KTree.node A10K2.u6385 (nat_lit 106350354) (nat_lit 14885023895) (nat_lit 0) A10K2.u6386 from rfl, totK_node, atot6385, atot6386]
  decide +kernel

theorem arows6390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6390 = true := by
  rw [show A10K2.u6390 = KTree.node A10K2.u6388 (nat_lit 106436721) (nat_lit 8224817192) (nat_lit 0) A10K2.u6389 from rfl, allE_node, arows6388, irow6390, arows6389]
  all_goals rfl

theorem atot6390 : totK PA10K2 A10K2.u6390 = [1299205790585, 5788790911665, 8283390568198, 4079850272250, 661284743978, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u6390 = KTree.node A10K2.u6388 (nat_lit 106436721) (nat_lit 8224817192) (nat_lit 0) A10K2.u6389 from rfl, totK_node, atot6388, atot6389]
  decide +kernel

theorem arows6399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6399 = true := by
  rw [show A10K2.u6399 = KTree.node A10K2.u6397 (nat_lit 106463586) (nat_lit 4024929769) (nat_lit 0) A10K2.u6398 from rfl, allE_node, arows6397, irow6399, arows6398]
  all_goals rfl

theorem atot6399 : totK PA10K2 A10K2.u6399 = [0, 1751644985363, 6728523825008, 7978742006810, 3090362666234, 459678735645, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u6399 = KTree.node A10K2.u6397 (nat_lit 106463586) (nat_lit 4024929769) (nat_lit 0) A10K2.u6398 from rfl, totK_node, atot6397, atot6398]
  decide +kernel

theorem arows6402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6402 = true := by
  rw [show A10K2.u6402 = KTree.node A10K2.u6400 (nat_lit 106491781) (nat_lit 2815247225) (nat_lit 0) A10K2.u6401 from rfl, allE_node, arows6400, irow6402, arows6401]
  all_goals rfl

theorem atot6402 : totK PA10K2 A10K2.u6402 = [838891203471, 4034052729916, 7089574028316, 5755934237684, 2024242230372, 235834083528, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u6402 = KTree.node A10K2.u6400 (nat_lit 106491781) (nat_lit 2815247225) (nat_lit 0) A10K2.u6401 from rfl, totK_node, atot6400, atot6401]
  decide +kernel

theorem arows6406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6406 = true := by
  rw [show A10K2.u6406 = KTree.node A10K2.u6404 (nat_lit 106514659) (nat_lit 10340699668) (nat_lit 0) A10K2.u6405 from rfl, allE_node, arows6404, irow6406, arows6405]
  all_goals rfl

theorem atot6406 : totK PA10K2 A10K2.u6406 = [1024751672328, 4871110306045, 7853189694885, 4616155524287, 846839780089, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u6406 = KTree.node A10K2.u6404 (nat_lit 106514659) (nat_lit 10340699668) (nat_lit 0) A10K2.u6405 from rfl, totK_node, atot6404, atot6405]
  decide +kernel

theorem arows6409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6409 = true := by
  rw [show A10K2.u6409 = KTree.node A10K2.u6407 (nat_lit 106528255) (nat_lit 14004808951) (nat_lit 0) A10K2.u6408 from rfl, allE_node, arows6407, irow6409, arows6408]
  all_goals rfl

theorem atot6409 : totK PA10K2 A10K2.u6409 = [319364795913, 2931467753312, 7674822322638, 7130449629469, 1930590636457, 102375354228, 0, 0, 0, 0] := by
  rw [show A10K2.u6409 = KTree.node A10K2.u6407 (nat_lit 106528255) (nat_lit 14004808951) (nat_lit 0) A10K2.u6408 from rfl, totK_node, atot6407, atot6408]
  decide +kernel

theorem arows6414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6414 = true := by
  rw [show A10K2.u6414 = KTree.node A10K2.u6412 (nat_lit 106547244) (nat_lit 13155048199) (nat_lit 0) A10K2.u6413 from rfl, allE_node, arows6412, irow6414, arows6413]
  all_goals rfl

theorem atot6414 : totK PA10K2 A10K2.u6414 = [0, 1023670636174, 4910653946280, 7784175280268, 4479845379619, 815494125337, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6414 = KTree.node A10K2.u6412 (nat_lit 106547244) (nat_lit 13155048199) (nat_lit 0) A10K2.u6413 from rfl, totK_node, atot6412, atot6413]
  decide +kernel

theorem arows6417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6417 = true := by
  rw [show A10K2.u6417 = KTree.node A10K2.u6415 (nat_lit 106630756) (nat_lit 7928653682) (nat_lit 0) A10K2.u6416 from rfl, allE_node, arows6415, irow6417, arows6416]
  all_goals rfl

theorem atot6417 : totK PA10K2 A10K2.u6417 = [1087413459552, 4893871084665, 7713204598505, 5028972682255, 1273145949850, 85718504641, 0, 0, 0, 0] := by
  rw [show A10K2.u6417 = KTree.node A10K2.u6415 (nat_lit 106630756) (nat_lit 7928653682) (nat_lit 0) A10K2.u6416 from rfl, totK_node, atot6415, atot6416]
  decide +kernel

theorem arows6421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6421 = true := by
  rw [show A10K2.u6421 = KTree.node A10K2.u6419 (nat_lit 106642679) (nat_lit 14641121806) (nat_lit 0) A10K2.u6420 from rfl, allE_node, arows6419, irow6421, arows6420]
  all_goals rfl

theorem atot6421 : totK PA10K2 A10K2.u6421 = [1259790066306, 5576499759493, 8102427975108, 4222673830169, 696136084677, 31677228370, 0, 0, 0, 0] := by
  rw [show A10K2.u6421 = KTree.node A10K2.u6419 (nat_lit 106642679) (nat_lit 14641121806) (nat_lit 0) A10K2.u6420 from rfl, totK_node, atot6419, atot6420]
  decide +kernel

theorem arows6424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6424 = true := by
  rw [show A10K2.u6424 = KTree.node A10K2.u6422 (nat_lit 106660364) (nat_lit 10947536199) (nat_lit 0) A10K2.u6423 from rfl, allE_node, arows6422, irow6424, arows6423]
  all_goals rfl

theorem atot6424 : totK PA10K2 A10K2.u6424 = [0, 1544189152251, 6368408704680, 8284916370545, 3515359656479, 415224354649, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6424 = KTree.node A10K2.u6422 (nat_lit 106660364) (nat_lit 10947536199) (nat_lit 0) A10K2.u6423 from rfl, totK_node, atot6422, atot6423]
  decide +kernel

theorem arows6430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6430 = true := by
  rw [show A10K2.u6430 = KTree.node A10K2.u6428 (nat_lit 106673882) (nat_lit 13850025289) (nat_lit 0) A10K2.u6429 from rfl, allE_node, arows6428, irow6430, arows6429]
  all_goals rfl

theorem atot6430 : totK PA10K2 A10K2.u6430 = [0, 1614798291031, 6403832741223, 8001207801170, 3406903746257, 389498530430, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6430 = KTree.node A10K2.u6428 (nat_lit 106673882) (nat_lit 13850025289) (nat_lit 0) A10K2.u6429 from rfl, totK_node, atot6428, atot6429]
  decide +kernel

theorem arows6433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6433 = true := by
  rw [show A10K2.u6433 = KTree.node A10K2.u6431 (nat_lit 106692552) (nat_lit 12150250187) (nat_lit 0) A10K2.u6432 from rfl, allE_node, arows6431, irow6433, arows6432]
  all_goals rfl

theorem atot6433 : totK PA10K2 A10K2.u6433 = [0, 776110475293, 4399975275629, 8117000512147, 5418007629124, 1115819530919, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u6433 = KTree.node A10K2.u6431 (nat_lit 106692552) (nat_lit 12150250187) (nat_lit 0) A10K2.u6432 from rfl, totK_node, atot6431, atot6432]
  decide +kernel

theorem arows6437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6437 = true := by
  rw [show A10K2.u6437 = KTree.node A10K2.u6435 (nat_lit 106720442) (nat_lit 14624595306) (nat_lit 0) A10K2.u6436 from rfl, allE_node, arows6435, irow6437, arows6436]
  all_goals rfl

theorem atot6437 : totK PA10K2 A10K2.u6437 = [0, 824587356464, 4325933919701, 7996308621144, 5808251024575, 1306103030455, 55817450081, 0, 0, 0] := by
  rw [show A10K2.u6437 = KTree.node A10K2.u6435 (nat_lit 106720442) (nat_lit 14624595306) (nat_lit 0) A10K2.u6436 from rfl, totK_node, atot6435, atot6436]
  decide +kernel

theorem arows6440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6440 = true := by
  rw [show A10K2.u6440 = KTree.node A10K2.u6438 (nat_lit 106730016) (nat_lit 14162460222) (nat_lit 0) A10K2.u6439 from rfl, allE_node, arows6438, irow6440, arows6439]
  all_goals rfl

theorem atot6440 : totK PA10K2 A10K2.u6440 = [0, 0, 1599461780806, 6476592070618, 8166861716222, 3320223142982, 390686673854, 7007974415, 0, 0] := by
  rw [show A10K2.u6440 = KTree.node A10K2.u6438 (nat_lit 106730016) (nat_lit 14162460222) (nat_lit 0) A10K2.u6439 from rfl, totK_node, atot6438, atot6439]
  decide +kernel

theorem arows6445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6445 = true := by
  rw [show A10K2.u6445 = KTree.node A10K2.u6443 (nat_lit 106771617) (nat_lit 5131293796) (nat_lit 0) A10K2.u6444 from rfl, allE_node, arows6443, irow6445, arows6444]
  all_goals rfl

theorem atot6445 : totK PA10K2 A10K2.u6445 = [0, 1160037459842, 5052686365942, 7497731117334, 4541019747966, 1061364649073, 75027878843, 0, 0, 0] := by
  rw [show A10K2.u6445 = KTree.node A10K2.u6443 (nat_lit 106771617) (nat_lit 5131293796) (nat_lit 0) A10K2.u6444 from rfl, totK_node, atot6443, atot6444]
  decide +kernel

theorem arows6448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6448 = true := by
  rw [show A10K2.u6448 = KTree.node A10K2.u6446 (nat_lit 106784488) (nat_lit 2930755110) (nat_lit 0) A10K2.u6447 from rfl, allE_node, arows6446, irow6448, arows6447]
  all_goals rfl

theorem atot6448 : totK PA10K2 A10K2.u6448 = [0, 1022970211870, 5080890723836, 8284131648869, 4728823414706, 756273525955, 19482267969, 0, 0, 0] := by
  rw [show A10K2.u6448 = KTree.node A10K2.u6446 (nat_lit 106784488) (nat_lit 2930755110) (nat_lit 0) A10K2.u6447 from rfl, totK_node, atot6446, atot6447]
  decide +kernel

theorem arows6452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6452 = true := by
  rw [show A10K2.u6452 = KTree.node A10K2.u6450 (nat_lit 106803092) (nat_lit 8113384784) (nat_lit 0) A10K2.u6451 from rfl, allE_node, arows6450, irow6452, arows6451]
  all_goals rfl

theorem atot6452 : totK PA10K2 A10K2.u6452 = [0, 0, 1494855639634, 6181903161923, 7943798432849, 3323545493605, 391032460102, 7151180950, 0, 0] := by
  rw [show A10K2.u6452 = KTree.node A10K2.u6450 (nat_lit 106803092) (nat_lit 8113384784) (nat_lit 0) A10K2.u6451 from rfl, totK_node, atot6450, atot6451]
  decide +kernel

theorem arows6455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6455 = true := by
  rw [show A10K2.u6455 = KTree.node A10K2.u6453 (nat_lit 106889991) (nat_lit 9765509339) (nat_lit 0) A10K2.u6454 from rfl, allE_node, arows6453, irow6455, arows6454]
  all_goals rfl

theorem atot6455 : totK PA10K2 A10K2.u6455 = [0, 756035837065, 4034641190949, 7791787186501, 6040023228446, 1529506630422, 80939540425, 0, 0, 0] := by
  rw [show A10K2.u6455 = KTree.node A10K2.u6453 (nat_lit 106889991) (nat_lit 9765509339) (nat_lit 0) A10K2.u6454 from rfl, totK_node, atot6453, atot6454]
  decide +kernel

theorem arows6462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6462 = true := by
  rw [show A10K2.u6462 = KTree.node A10K2.u6460 (nat_lit 106903316) (nat_lit 11547944041) (nat_lit 0) A10K2.u6461 from rfl, allE_node, arows6460, irow6462, arows6461]
  all_goals rfl

theorem atot6462 : totK PA10K2 A10K2.u6462 = [0, 1457040347446, 5958280417771, 7982067657321, 3874445118963, 537320398675, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u6462 = KTree.node A10K2.u6460 (nat_lit 106903316) (nat_lit 11547944041) (nat_lit 0) A10K2.u6461 from rfl, totK_node, atot6460, atot6461]
  decide +kernel

theorem arows6465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6465 = true := by
  rw [show A10K2.u6465 = KTree.node A10K2.u6463 (nat_lit 106921569) (nat_lit 3847208183) (nat_lit 0) A10K2.u6464 from rfl, allE_node, arows6463, irow6465, arows6464]
  all_goals rfl

theorem atot6465 : totK PA10K2 A10K2.u6465 = [0, 122956571035, 2352939879891, 7262388003885, 7595733321728, 2553432662244, 198600782101, 0, 0, 0] := by
  rw [show A10K2.u6465 = KTree.node A10K2.u6463 (nat_lit 106921569) (nat_lit 3847208183) (nat_lit 0) A10K2.u6464 from rfl, totK_node, atot6463, atot6464]
  decide +kernel

theorem arows6469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6469 = true := by
  rw [show A10K2.u6469 = KTree.node A10K2.u6467 (nat_lit 106934256) (nat_lit 13223236894) (nat_lit 0) A10K2.u6468 from rfl, allE_node, arows6467, irow6469, arows6468]
  all_goals rfl

theorem atot6469 : totK PA10K2 A10K2.u6469 = [0, 0, 1327304203012, 5896279568734, 8254463266359, 3807515094186, 456980044659, 12758098799, 0, 0] := by
  rw [show A10K2.u6469 = KTree.node A10K2.u6467 (nat_lit 106934256) (nat_lit 13223236894) (nat_lit 0) A10K2.u6468 from rfl, totK_node, atot6467, atot6468]
  decide +kernel

theorem arows6472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6472 = true := by
  rw [show A10K2.u6472 = KTree.node A10K2.u6470 (nat_lit 106954182) (nat_lit 15836379956) (nat_lit 0) A10K2.u6471 from rfl, allE_node, arows6470, irow6472, arows6471]
  all_goals rfl

theorem atot6472 : totK PA10K2 A10K2.u6472 = [0, 872244600920, 3409392246891, 5167218448435, 5383107315833, 3799608217562, 961189328672, 61018386929, 0, 0] := by
  rw [show A10K2.u6472 = KTree.node A10K2.u6470 (nat_lit 106954182) (nat_lit 15836379956) (nat_lit 0) A10K2.u6471 from rfl, totK_node, atot6470, atot6471]
  decide +kernel

theorem arows6477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6477 = true := by
  rw [show A10K2.u6477 = KTree.node A10K2.u6475 (nat_lit 107562208) (nat_lit 7525496256) (nat_lit 0) A10K2.u6476 from rfl, allE_node, arows6475, irow6477, arows6476]
  all_goals rfl

theorem atot6477 : totK PA10K2 A10K2.u6477 = [0, 683621691564, 4155202854049, 7954198310249, 5024471927519, 815466938586, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6477 = KTree.node A10K2.u6475 (nat_lit 107562208) (nat_lit 7525496256) (nat_lit 0) A10K2.u6476 from rfl, totK_node, atot6475, atot6476]
  decide +kernel

theorem arows6480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6480 = true := by
  rw [show A10K2.u6480 = KTree.node A10K2.u6478 (nat_lit 107574445) (nat_lit 5497033346) (nat_lit 0) A10K2.u6479 from rfl, allE_node, arows6478, irow6480, arows6479]
  all_goals rfl

theorem atot6480 : totK PA10K2 A10K2.u6480 = [0, 788312884667, 4189851009837, 7744390756390, 5819756202624, 1484187243749, 80373590639, 0, 0, 0] := by
  rw [show A10K2.u6480 = KTree.node A10K2.u6478 (nat_lit 107574445) (nat_lit 5497033346) (nat_lit 0) A10K2.u6479 from rfl, totK_node, atot6478, atot6479]
  decide +kernel

theorem arows6484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6484 = true := by
  rw [show A10K2.u6484 = KTree.node A10K2.u6482 (nat_lit 107592534) (nat_lit 8341228601) (nat_lit 0) A10K2.u6483 from rfl, allE_node, arows6482, irow6484, arows6483]
  all_goals rfl

theorem atot6484 : totK PA10K2 A10K2.u6484 = [0, 0, 1050260430285, 5200403298969, 7838718327379, 3933423025491, 648566861788, 31082886609, 0, 0] := by
  rw [show A10K2.u6484 = KTree.node A10K2.u6482 (nat_lit 107592534) (nat_lit 8341228601) (nat_lit 0) A10K2.u6483 from rfl, totK_node, atot6482, atot6483]
  decide +kernel

theorem arows6487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6487 = true := by
  rw [show A10K2.u6487 = KTree.node A10K2.u6485 (nat_lit 107605616) (nat_lit 13824277441) (nat_lit 0) A10K2.u6486 from rfl, allE_node, arows6485, irow6487, arows6486]
  all_goals rfl

theorem atot6487 : totK PA10K2 A10K2.u6487 = [0, 724179001030, 3453344021597, 6524053127773, 5972324282199, 2265352343966, 253715152747, 6121173289, 0, 0] := by
  rw [show A10K2.u6487 = KTree.node A10K2.u6485 (nat_lit 107605616) (nat_lit 13824277441) (nat_lit 0) A10K2.u6486 from rfl, totK_node, atot6485, atot6486]
  decide +kernel

theorem arows6493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6493 = true := by
  rw [show A10K2.u6493 = KTree.node A10K2.u6491 (nat_lit 107625659) (nat_lit 7140223799) (nat_lit 0) A10K2.u6492 from rfl, allE_node, arows6491, irow6493, arows6492]
  all_goals rfl

theorem atot6493 : totK PA10K2 A10K2.u6493 = [0, 1069298865517, 5182271197508, 7968373902456, 4319873618200, 729136718473, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6493 = KTree.node A10K2.u6491 (nat_lit 107625659) (nat_lit 7140223799) (nat_lit 0) A10K2.u6492 from rfl, totK_node, atot6491, atot6492]
  decide +kernel

theorem arows6496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6496 = true := by
  rw [show A10K2.u6496 = KTree.node A10K2.u6494 (nat_lit 107653310) (nat_lit 13001525521) (nat_lit 0) A10K2.u6495 from rfl, allE_node, arows6494, irow6496, arows6495]
  all_goals rfl

theorem atot6496 : totK PA10K2 A10K2.u6496 = [0, 0, 2244817954088, 7695847658646, 7251454833949, 1713259392094, 83006932295, 0, 0, 0] := by
  rw [show A10K2.u6496 = KTree.node A10K2.u6494 (nat_lit 107653310) (nat_lit 13001525521) (nat_lit 0) A10K2.u6495 from rfl, totK_node, atot6494, atot6495]
  decide +kernel

theorem arows6500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6500 = true := by
  rw [show A10K2.u6500 = KTree.node A10K2.u6498 (nat_lit 107679308) (nat_lit 5234987898) (nat_lit 0) A10K2.u6499 from rfl, allE_node, arows6498, irow6500, arows6499]
  all_goals rfl

theorem atot6500 : totK PA10K2 A10K2.u6500 = [0, 1096783676597, 4419933353834, 6786807987113, 5267621891776, 1842664515858, 221834824700, 6354482628, 0, 0] := by
  rw [show A10K2.u6500 = KTree.node A10K2.u6498 (nat_lit 107679308) (nat_lit 5234987898) (nat_lit 0) A10K2.u6499 from rfl, totK_node, atot6498, atot6499]
  decide +kernel

theorem arows6503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6503 = true := by
  rw [show A10K2.u6503 = KTree.node A10K2.u6501 (nat_lit 107700330) (nat_lit 11933677) (nat_lit 0) A10K2.u6502 from rfl, allE_node, arows6501, irow6503, arows6502]
  all_goals rfl

theorem atot6503 : totK PA10K2 A10K2.u6503 = [0, 1073653283149, 5108777605297, 8149742056614, 4764944952259, 860519660414, 38334182947, 0, 0, 0] := by
  rw [show A10K2.u6503 = KTree.node A10K2.u6501 (nat_lit 107700330) (nat_lit 11933677) (nat_lit 0) A10K2.u6502 from rfl, totK_node, atot6501, atot6502]
  decide +kernel

theorem arows6508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6508 = true := by
  rw [show A10K2.u6508 = KTree.node A10K2.u6506 (nat_lit 107712013) (nat_lit 2992582619) (nat_lit 0) A10K2.u6507 from rfl, allE_node, arows6506, irow6508, arows6507]
  all_goals rfl

theorem atot6508 : totK PA10K2 A10K2.u6508 = [0, 0, 1889245472915, 7159903526725, 8146814817968, 2784816056965, 204318102360, 0, 0, 0] := by
  rw [show A10K2.u6508 = KTree.node A10K2.u6506 (nat_lit 107712013) (nat_lit 2992582619) (nat_lit 0) A10K2.u6507 from rfl, totK_node, atot6506, atot6507]
  decide +kernel

theorem arows6511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6511 = true := by
  rw [show A10K2.u6511 = KTree.node A10K2.u6509 (nat_lit 107734244) (nat_lit 10731268925) (nat_lit 0) A10K2.u6510 from rfl, allE_node, arows6509, irow6511, arows6510]
  all_goals rfl

theorem atot6511 : totK PA10K2 A10K2.u6511 = [0, 0, 890760947148, 4995108300699, 8551597023976, 4879875748745, 674151266184, 13204174009, 0, 0] := by
  rw [show A10K2.u6511 = KTree.node A10K2.u6509 (nat_lit 107734244) (nat_lit 10731268925) (nat_lit 0) A10K2.u6510 from rfl, totK_node, atot6509, atot6510]
  decide +kernel

theorem arows6515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6515 = true := by
  rw [show A10K2.u6515 = KTree.node A10K2.u6513 (nat_lit 107818386) (nat_lit 15259374986) (nat_lit 0) A10K2.u6514 from rfl, allE_node, arows6513, irow6515, arows6514]
  all_goals rfl

theorem atot6515 : totK PA10K2 A10K2.u6515 = [0, 0, 982280176159, 4635202579489, 7521270229827, 4881026797900, 1105752315980, 66741895322, 0, 0] := by
  rw [show A10K2.u6515 = KTree.node A10K2.u6513 (nat_lit 107818386) (nat_lit 15259374986) (nat_lit 0) A10K2.u6514 from rfl, totK_node, atot6513, atot6514]
  decide +kernel

theorem arows6518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6518 = true := by
  rw [show A10K2.u6518 = KTree.node A10K2.u6516 (nat_lit 107829591) (nat_lit 4563600352) (nat_lit 0) A10K2.u6517 from rfl, allE_node, arows6516, irow6518, arows6517]
  all_goals rfl

theorem atot6518 : totK PA10K2 A10K2.u6518 = [0, 0, 1345328717393, 5881809270444, 8060507050698, 3439881643707, 364823285889, 6239673734, 0, 0] := by
  rw [show A10K2.u6518 = KTree.node A10K2.u6516 (nat_lit 107829591) (nat_lit 4563600352) (nat_lit 0) A10K2.u6517 from rfl, totK_node, atot6516, atot6517]
  decide +kernel

theorem arows6526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6526 = true := by
  rw [show A10K2.u6526 = KTree.node A10K2.u6524 (nat_lit 107850497) (nat_lit 7014985579) (nat_lit 0) A10K2.u6525 from rfl, allE_node, arows6524, irow6526, arows6525]
  all_goals rfl

theorem atot6526 : totK PA10K2 A10K2.u6526 = [0, 0, 0, 1324950998838, 5754921841637, 7736721821108, 3659820372095, 611430749881, 31018567651, 0] := by
  rw [show A10K2.u6526 = KTree.node A10K2.u6524 (nat_lit 107850497) (nat_lit 7014985579) (nat_lit 0) A10K2.u6525 from rfl, totK_node, atot6524, atot6525]
  decide +kernel

theorem arows6529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6529 = true := by
  rw [show A10K2.u6529 = KTree.node A10K2.u6527 (nat_lit 107862248) (nat_lit 6883156831) (nat_lit 0) A10K2.u6528 from rfl, allE_node, arows6527, irow6529, arows6528]
  all_goals rfl

theorem atot6529 : totK PA10K2 A10K2.u6529 = [0, 0, 251986720587, 2347856120830, 6381876562361, 6867732610560, 2489081247963, 273914754757, 5685526223, 0] := by
  rw [show A10K2.u6529 = KTree.node A10K2.u6527 (nat_lit 107862248) (nat_lit 6883156831) (nat_lit 0) A10K2.u6528 from rfl, totK_node, atot6527, atot6528]
  decide +kernel

theorem arows6533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6533 = true := by
  rw [show A10K2.u6533 = KTree.node A10K2.u6531 (nat_lit 107884442) (nat_lit 14591627111) (nat_lit 0) A10K2.u6532 from rfl, allE_node, arows6531, irow6533, arows6532]
  all_goals rfl

theorem atot6533 : totK PA10K2 A10K2.u6533 = [0, 0, 1177199756201, 5080076890694, 7701554705798, 4367188357363, 759515505445, 37229241746, 0, 0] := by
  rw [show A10K2.u6533 = KTree.node A10K2.u6531 (nat_lit 107884442) (nat_lit 14591627111) (nat_lit 0) A10K2.u6532 from rfl, totK_node, atot6531, atot6532]
  decide +kernel

theorem arows6536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6536 = true := by
  rw [show A10K2.u6536 = KTree.node A10K2.u6534 (nat_lit 107907107) (nat_lit 7997727697) (nat_lit 0) A10K2.u6535 from rfl, allE_node, arows6534, irow6536, arows6535]
  all_goals rfl

theorem atot6536 : totK PA10K2 A10K2.u6536 = [0, 0, 358002183444, 3403293339779, 7970436302836, 5863363849827, 1150965357574, 51706745138, 0, 0] := by
  rw [show A10K2.u6536 = KTree.node A10K2.u6534 (nat_lit 107907107) (nat_lit 7997727697) (nat_lit 0) A10K2.u6535 from rfl, totK_node, atot6534, atot6535]
  decide +kernel

theorem arows6541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6541 = true := by
  rw [show A10K2.u6541 = KTree.node A10K2.u6539 (nat_lit 107927781) (nat_lit 7136786097) (nat_lit 0) A10K2.u6540 from rfl, allE_node, arows6539, irow6541, arows6540]
  all_goals rfl

theorem atot6541 : totK PA10K2 A10K2.u6541 = [0, 0, 1018983537682, 3984044071652, 6376696671831, 5571833516757, 1885208263334, 225229248886, 5982052406, 0] := by
  rw [show A10K2.u6541 = KTree.node A10K2.u6539 (nat_lit 107927781) (nat_lit 7136786097) (nat_lit 0) A10K2.u6540 from rfl, totK_node, atot6539, atot6540]
  decide +kernel

theorem arows6544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6544 = true := by
  rw [show A10K2.u6544 = KTree.node A10K2.u6542 (nat_lit 107962425) (nat_lit 7321262860) (nat_lit 0) A10K2.u6543 from rfl, allE_node, arows6542, irow6544, arows6543]
  all_goals rfl

theorem atot6544 : totK PA10K2 A10K2.u6544 = [0, 0, 1143399010272, 5609060137587, 8453957886004, 4156073238792, 608599221199, 25660650750, 0, 0] := by
  rw [show A10K2.u6544 = KTree.node A10K2.u6542 (nat_lit 107962425) (nat_lit 7321262860) (nat_lit 0) A10K2.u6543 from rfl, totK_node, atot6542, atot6543]
  decide +kernel

theorem arows6548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6548 = true := by
  rw [show A10K2.u6548 = KTree.node A10K2.u6546 (nat_lit 108079895) (nat_lit 7574462884) (nat_lit 0) A10K2.u6547 from rfl, allE_node, arows6546, irow6548, arows6547]
  all_goals rfl

theorem atot6548 : totK PA10K2 A10K2.u6548 = [0, 842026830166, 3922294004563, 6455250686170, 5119962821980, 2560050701901, 626330091317, 41590655314, 0, 0] := by
  rw [show A10K2.u6548 = KTree.node A10K2.u6546 (nat_lit 108079895) (nat_lit 7574462884) (nat_lit 0) A10K2.u6547 from rfl, totK_node, atot6546, atot6547]
  decide +kernel

theorem arows6551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6551 = true := by
  rw [show A10K2.u6551 = KTree.node A10K2.u6549 (nat_lit 108090725) (nat_lit 7280085236) (nat_lit 0) A10K2.u6550 from rfl, allE_node, arows6549, irow6551, arows6550]
  all_goals rfl

theorem atot6551 : totK PA10K2 A10K2.u6551 = [0, 1345953382226, 5825154807929, 8067808392021, 3716686931853, 445038305703, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6551 = KTree.node A10K2.u6549 (nat_lit 108090725) (nat_lit 7280085236) (nat_lit 0) A10K2.u6550 from rfl, totK_node, atot6549, atot6550]
  decide +kernel

theorem arows6557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6557 = true := by
  rw [show A10K2.u6557 = KTree.node A10K2.u6555 (nat_lit 108112549) (nat_lit 7210046638) (nat_lit 0) A10K2.u6556 from rfl, allE_node, arows6555, irow6557, arows6556]
  all_goals rfl

theorem atot6557 : totK PA10K2 A10K2.u6557 = [0, 0, 1270576742605, 5686635519608, 8021334646043, 3817088348937, 617131549402, 31082886609, 0, 0] := by
  rw [show A10K2.u6557 = KTree.node A10K2.u6555 (nat_lit 108112549) (nat_lit 7210046638) (nat_lit 0) A10K2.u6556 from rfl, totK_node, atot6555, atot6556]
  decide +kernel

theorem arows6560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6560 = true := by
  rw [show A10K2.u6560 = KTree.node A10K2.u6558 (nat_lit 108123632) (nat_lit 5810104385) (nat_lit 0) A10K2.u6559 from rfl, allE_node, arows6558, irow6560, arows6559]
  all_goals rfl

theorem atot6560 : totK PA10K2 A10K2.u6560 = [0, 247698060303, 1947053265858, 5967257012867, 7548059689133, 3158972916532, 336524085398, 6121173289, 0, 0] := by
  rw [show A10K2.u6560 = KTree.node A10K2.u6558 (nat_lit 108123632) (nat_lit 5810104385) (nat_lit 0) A10K2.u6559 from rfl, totK_node, atot6558, atot6559]
  decide +kernel

theorem arows6564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6564 = true := by
  rw [show A10K2.u6564 = KTree.node A10K2.u6562 (nat_lit 108143848) (nat_lit 5999041071) (nat_lit 0) A10K2.u6563 from rfl, allE_node, arows6562, irow6564, arows6563]
  all_goals rfl

theorem atot6564 : totK PA10K2 A10K2.u6564 = [0, 1080606140671, 5078972162570, 7809079474219, 4338946860271, 834057233697, 50742966146, 0, 0, 0] := by
  rw [show A10K2.u6564 = KTree.node A10K2.u6562 (nat_lit 108143848) (nat_lit 5999041071) (nat_lit 0) A10K2.u6563 from rfl, totK_node, atot6562, atot6563]
  decide +kernel

theorem arows6567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6567 = true := by
  rw [show A10K2.u6567 = KTree.node A10K2.u6565 (nat_lit 108152988) (nat_lit 11901295526) (nat_lit 0) A10K2.u6566 from rfl, allE_node, arows6565, irow6567, arows6566]
  all_goals rfl

theorem atot6567 : totK PA10K2 A10K2.u6567 = [0, 820824437048, 4542789054543, 8031772408061, 4773585728028, 773411460748, 37599984045, 0, 0, 0] := by
  rw [show A10K2.u6567 = KTree.node A10K2.u6565 (nat_lit 108152988) (nat_lit 11901295526) (nat_lit 0) A10K2.u6566 from rfl, totK_node, atot6565, atot6566]
  decide +kernel

theorem arows6572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6572 = true := by
  rw [show A10K2.u6572 = KTree.node A10K2.u6570 (nat_lit 108178936) (nat_lit 10504776075) (nat_lit 0) A10K2.u6571 from rfl, allE_node, arows6570, irow6572, arows6571]
  all_goals rfl

theorem atot6572 : totK PA10K2 A10K2.u6572 = [0, 0, 1863874843043, 7101184202561, 7755134901324, 2124606979161, 127220762566, 0, 0, 0] := by
  rw [show A10K2.u6572 = KTree.node A10K2.u6570 (nat_lit 108178936) (nat_lit 10504776075) (nat_lit 0) A10K2.u6571 from rfl, totK_node, atot6570, atot6571]
  decide +kernel

theorem arows6575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6575 = true := by
  rw [show A10K2.u6575 = KTree.node A10K2.u6573 (nat_lit 108342122) (nat_lit 9087513361) (nat_lit 0) A10K2.u6574 from rfl, allE_node, arows6573, irow6575, arows6574]
  all_goals rfl

theorem atot6575 : totK PA10K2 A10K2.u6575 = [0, 0, 915705225837, 4625250624456, 7916950050560, 4689278253244, 853729417844, 37807056478, 0, 0] := by
  rw [show A10K2.u6575 = KTree.node A10K2.u6573 (nat_lit 108342122) (nat_lit 9087513361) (nat_lit 0) A10K2.u6574 from rfl, totK_node, atot6573, atot6574]
  decide +kernel

theorem arows6579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6579 = true := by
  rw [show A10K2.u6579 = KTree.node A10K2.u6577 (nat_lit 108353580) (nat_lit 13155048199) (nat_lit 0) A10K2.u6578 from rfl, allE_node, arows6577, irow6579, arows6578]
  all_goals rfl

theorem atot6579 : totK PA10K2 A10K2.u6579 = [0, 0, 1272274986555, 5829039729104, 8253432718072, 3572454193353, 367387495114, 6354482628, 0, 0] := by
  rw [show A10K2.u6579 = KTree.node A10K2.u6577 (nat_lit 108353580) (nat_lit 13155048199) (nat_lit 0) A10K2.u6578 from rfl, totK_node, atot6577, atot6578]
  decide +kernel

theorem arows6582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6582 = true := by
  rw [show A10K2.u6582 = KTree.node A10K2.u6580 (nat_lit 108402848) (nat_lit 9047594617) (nat_lit 0) A10K2.u6581 from rfl, allE_node, arows6580, irow6582, arows6581]
  all_goals rfl

theorem atot6582 : totK PA10K2 A10K2.u6582 = [0, 0, 1327305504860, 5790235800137, 8032611246042, 3618493715508, 490904836610, 12423235244, 0, 0] := by
  rw [show A10K2.u6582 = KTree.node A10K2.u6580 (nat_lit 108402848) (nat_lit 9047594617) (nat_lit 0) A10K2.u6581 from rfl, totK_node, atot6580, atot6581]
  decide +kernel

theorem arows6589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6589 = true := by
  rw [show A10K2.u6589 = KTree.node A10K2.u6587 (nat_lit 108414620) (nat_lit 11283911090) (nat_lit 0) A10K2.u6588 from rfl, allE_node, arows6587, irow6589, arows6588]
  all_goals rfl

theorem atot6589 : totK PA10K2 A10K2.u6589 = [0, 0, 819213633141, 4544227367678, 7970636206798, 4515738707067, 779763046547, 37357927314, 0, 0] := by
  rw [show A10K2.u6589 = KTree.node A10K2.u6587 (nat_lit 108414620) (nat_lit 11283911090) (nat_lit 0) A10K2.u6588 from rfl, totK_node, atot6587, atot6588]
  decide +kernel

theorem arows6592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6592 = true := by
  rw [show A10K2.u6592 = KTree.node A10K2.u6590 (nat_lit 108440385) (nat_lit 5321145188) (nat_lit 0) A10K2.u6591 from rfl, allE_node, arows6590, irow6592, arows6591]
  all_goals rfl

theorem atot6592 : totK PA10K2 A10K2.u6592 = [0, 0, 0, 2013452196667, 7478733005571, 7190622082090, 1705995551331, 92473238738, 0, 0] := by
  rw [show A10K2.u6592 = KTree.node A10K2.u6590 (nat_lit 108440385) (nat_lit 5321145188) (nat_lit 0) A10K2.u6591 from rfl, totK_node, atot6590, atot6591]
  decide +kernel

theorem arows6596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6596 = true := by
  rw [show A10K2.u6596 = KTree.node A10K2.u6594 (nat_lit 108531143) (nat_lit 14470067458) (nat_lit 0) A10K2.u6595 from rfl, allE_node, arows6594, irow6596, arows6595]
  all_goals rfl

theorem atot6596 : totK PA10K2 A10K2.u6596 = [0, 1061249591977, 4614276391489, 6522812730172, 3762821396178, 2135511884974, 1123462611940, 203361510298, 6354482628, 0] := by
  rw [show A10K2.u6596 = KTree.node A10K2.u6594 (nat_lit 108531143) (nat_lit 14470067458) (nat_lit 0) A10K2.u6595 from rfl, totK_node, atot6594, atot6595]
  decide +kernel

theorem arows6599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6599 = true := by
  rw [show A10K2.u6599 = KTree.node A10K2.u6597 (nat_lit 108558234) (nat_lit 14678122636) (nat_lit 0) A10K2.u6598 from rfl, allE_node, arows6597, irow6599, arows6598]
  all_goals rfl

theorem atot6599 : totK PA10K2 A10K2.u6599 = [0, 541450865991, 3638252655231, 7987456324698, 6550769895180, 1611845499491, 93930932821, 0, 0, 0] := by
  rw [show A10K2.u6599 = KTree.node A10K2.u6597 (nat_lit 108558234) (nat_lit 14678122636) (nat_lit 0) A10K2.u6598 from rfl, totK_node, atot6597, atot6598]
  decide +kernel

theorem arows6604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6604 = true := by
  rw [show A10K2.u6604 = KTree.node A10K2.u6602 (nat_lit 108586652) (nat_lit 9499857603) (nat_lit 0) A10K2.u6603 from rfl, allE_node, arows6602, irow6604, arows6603]
  all_goals rfl

theorem atot6604 : totK PA10K2 A10K2.u6604 = [0, 628127599786, 2995708859839, 6180001411973, 6695670497637, 2925097988220, 361497947669, 7237400819, 0, 0] := by
  rw [show A10K2.u6604 = KTree.node A10K2.u6602 (nat_lit 108586652) (nat_lit 9499857603) (nat_lit 0) A10K2.u6603 from rfl, totK_node, atot6602, atot6603]
  decide +kernel

theorem arows6607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6607 = true := by
  rw [show A10K2.u6607 = KTree.node A10K2.u6605 (nat_lit 108610732) (nat_lit 12833588919) (nat_lit 0) A10K2.u6606 from rfl, allE_node, arows6605, irow6607, arows6606]
  all_goals rfl

theorem atot6607 : totK PA10K2 A10K2.u6607 = [0, 940054043234, 4713979590144, 7942223557662, 4818079731262, 850605654845, 37750801259, 0, 0, 0] := by
  rw [show A10K2.u6607 = KTree.node A10K2.u6605 (nat_lit 108610732) (nat_lit 12833588919) (nat_lit 0) A10K2.u6606 from rfl, totK_node, atot6605, atot6606]
  decide +kernel

theorem arows6611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6611 = true := by
  rw [show A10K2.u6611 = KTree.node A10K2.u6609 (nat_lit 108623205) (nat_lit 6803922604) (nat_lit 0) A10K2.u6610 from rfl, allE_node, arows6609, irow6611, arows6610]
  all_goals rfl

theorem atot6611 : totK PA10K2 A10K2.u6611 = [0, 614826028692, 3813045568925, 7902948691949, 6122293646175, 1509895734465, 89191227119, 0, 0, 0] := by
  rw [show A10K2.u6611 = KTree.node A10K2.u6609 (nat_lit 108623205) (nat_lit 6803922604) (nat_lit 0) A10K2.u6610 from rfl, totK_node, atot6609, atot6610]
  decide +kernel

theorem arows6614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6614 = true := by
  rw [show A10K2.u6614 = KTree.node A10K2.u6612 (nat_lit 108641720) (nat_lit 12515046275) (nat_lit 0) A10K2.u6613 from rfl, allE_node, arows6612, irow6614, arows6613]
  all_goals rfl

theorem atot6614 : totK PA10K2 A10K2.u6614 = [0, 0, 963550082898, 4747134477863, 7851244453050, 4517965317405, 796654080257, 36968589557, 0, 0] := by
  rw [show A10K2.u6614 = KTree.node A10K2.u6612 (nat_lit 108641720) (nat_lit 12515046275) (nat_lit 0) A10K2.u6613 from rfl, totK_node, atot6612, atot6613]
  decide +kernel

theorem arows6620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6620 = true := by
  rw [show A10K2.u6620 = KTree.node A10K2.u6618 (nat_lit 108725036) (nat_lit 8854499309) (nat_lit 0) A10K2.u6619 from rfl, allE_node, arows6618, irow6620, arows6619]
  all_goals rfl

theorem atot6620 : totK PA10K2 A10K2.u6620 = [0, 797356829707, 4084086350276, 7766856605636, 5975008041888, 1567022201185, 95446986272, 0, 0, 0] := by
  rw [show A10K2.u6620 = KTree.node A10K2.u6618 (nat_lit 108725036) (nat_lit 8854499309) (nat_lit 0) A10K2.u6619 from rfl, totK_node, atot6618, atot6619]
  decide +kernel

theorem arows6623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6623 = true := by
  rw [show A10K2.u6623 = KTree.node A10K2.u6621 (nat_lit 108738330) (nat_lit 14325366193) (nat_lit 0) A10K2.u6622 from rfl, allE_node, arows6621, irow6623, arows6622]
  all_goals rfl

theorem atot6623 : totK PA10K2 A10K2.u6623 = [0, 1337417859817, 5723382750030, 7965774965572, 4012704626115, 667021391365, 31452269383, 0, 0, 0] := by
  rw [show A10K2.u6623 = KTree.node A10K2.u6621 (nat_lit 108738330) (nat_lit 14325366193) (nat_lit 0) A10K2.u6622 from rfl, totK_node, atot6621, atot6622]
  decide +kernel

theorem arows6627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6627 = true := by
  rw [show A10K2.u6627 = KTree.node A10K2.u6625 (nat_lit 108756520) (nat_lit 11782639116) (nat_lit 0) A10K2.u6626 from rfl, allE_node, arows6625, irow6627, arows6626]
  all_goals rfl

theorem atot6627 : totK PA10K2 A10K2.u6627 = [0, 203085421841, 2492941940849, 7298935314322, 7536853557486, 2458721901770, 174609012262, 0, 0, 0] := by
  rw [show A10K2.u6627 = KTree.node A10K2.u6625 (nat_lit 108756520) (nat_lit 11782639116) (nat_lit 0) A10K2.u6626 from rfl, totK_node, atot6625, atot6626]
  decide +kernel

theorem arows6630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6630 = true := by
  rw [show A10K2.u6630 = KTree.node A10K2.u6628 (nat_lit 108768981) (nat_lit 5471119522) (nat_lit 0) A10K2.u6629 from rfl, allE_node, arows6628, irow6630, arows6629]
  all_goals rfl

theorem atot6630 : totK PA10K2 A10K2.u6630 = [0, 0, 1332010740447, 5759551662317, 8087933138687, 4029326950941, 553929437976, 13679205470, 0, 0] := by
  rw [show A10K2.u6630 = KTree.node A10K2.u6628 (nat_lit 108768981) (nat_lit 5471119522) (nat_lit 0) A10K2.u6629 from rfl, totK_node, atot6628, atot6629]
  decide +kernel

theorem arows6635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6635 = true := by
  rw [show A10K2.u6635 = KTree.node A10K2.u6633 (nat_lit 108788793) (nat_lit 7218615403) (nat_lit 0) A10K2.u6634 from rfl, allE_node, arows6633, irow6635, arows6634]
  all_goals rfl

theorem atot6635 : totK PA10K2 A10K2.u6635 = [829926626583, 2621449508646, 2717452354845, 2964630993755, 5276729920372, 4092823177300, 979638778335, 61110126106, 0, 0] := by
  rw [show A10K2.u6635 = KTree.node A10K2.u6633 (nat_lit 108788793) (nat_lit 7218615403) (nat_lit 0) A10K2.u6634 from rfl, totK_node, atot6633, atot6634]
  decide +kernel

theorem arows6638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6638 = true := by
  rw [show A10K2.u6638 = KTree.node A10K2.u6636 (nat_lit 113262919) (nat_lit 5865904567) (nat_lit 0) A10K2.u6637 from rfl, allE_node, arows6636, irow6638, arows6637]
  all_goals rfl

theorem atot6638 : totK PA10K2 A10K2.u6638 = [785339288605, 4450462425329, 7950572953400, 4846751980334, 860748434446, 37186156514, 0, 0, 0, 0] := by
  rw [show A10K2.u6638 = KTree.node A10K2.u6636 (nat_lit 113262919) (nat_lit 5865904567) (nat_lit 0) A10K2.u6637 from rfl, totK_node, atot6636, atot6637]
  decide +kernel

theorem arows6642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6642 = true := by
  rw [show A10K2.u6642 = KTree.node A10K2.u6640 (nat_lit 113276053) (nat_lit 4779000371) (nat_lit 0) A10K2.u6641 from rfl, allE_node, arows6640, irow6642, arows6641]
  all_goals rfl

theorem atot6642 : totK PA10K2 A10K2.u6642 = [616560319149, 3845170299171, 7919076398698, 6077346610532, 1489929930378, 88582086806, 0, 0, 0, 0] := by
  rw [show A10K2.u6642 = KTree.node A10K2.u6640 (nat_lit 113276053) (nat_lit 4779000371) (nat_lit 0) A10K2.u6641 from rfl, totK_node, atot6640, atot6641]
  decide +kernel

theorem arows6645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6645 = true := by
  rw [show A10K2.u6645 = KTree.node A10K2.u6643 (nat_lit 113286582) (nat_lit 17044428830) (nat_lit 0) A10K2.u6644 from rfl, allE_node, arows6643, irow6645, arows6644]
  all_goals rfl

theorem atot6645 : totK PA10K2 A10K2.u6645 = [0, 871937490768, 4702687597629, 7978192379102, 4384478054092, 705420901237, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6645 = KTree.node A10K2.u6643 (nat_lit 113286582) (nat_lit 17044428830) (nat_lit 0) A10K2.u6644 from rfl, totK_node, atot6643, atot6644]
  decide +kernel

theorem arows6655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6655 = true := by
  rw [show A10K2.u6655 = KTree.node A10K2.u6653 (nat_lit 113377793) (nat_lit 10582213929) (nat_lit 0) A10K2.u6654 from rfl, allE_node, arows6653, irow6655, arows6654]
  all_goals rfl

theorem atot6655 : totK PA10K2 A10K2.u6655 = [759554354984, 4073820836131, 7519622155347, 5618771602917, 1648533602981, 183579293449, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6655 = KTree.node A10K2.u6653 (nat_lit 113377793) (nat_lit 10582213929) (nat_lit 0) A10K2.u6654 from rfl, totK_node, atot6653, atot6654]
  decide +kernel

theorem arows6658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6658 = true := by
  rw [show A10K2.u6658 = KTree.node A10K2.u6656 (nat_lit 113399954) (nat_lit 15203200646) (nat_lit 0) A10K2.u6657 from rfl, allE_node, arows6656, irow6658, arows6657]
  all_goals rfl

theorem atot6658 : totK PA10K2 A10K2.u6658 = [559395152186, 3712877688612, 7859573896917, 5903264853227, 1246816406275, 50598160790, 0, 0, 0, 0] := by
  rw [show A10K2.u6658 = KTree.node A10K2.u6656 (nat_lit 113399954) (nat_lit 15203200646) (nat_lit 0) A10K2.u6657 from rfl, totK_node, atot6656, atot6657]
  decide +kernel

theorem arows6662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6662 = true := by
  rw [show A10K2.u6662 = KTree.node A10K2.u6660 (nat_lit 113443248) (nat_lit 14711657310) (nat_lit 0) A10K2.u6661 from rfl, allE_node, arows6660, irow6662, arows6661]
  all_goals rfl

theorem atot6662 : totK PA10K2 A10K2.u6662 = [793104720795, 3708363244356, 6666133551875, 5712760234551, 2061218828485, 289599722313, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6662 = KTree.node A10K2.u6660 (nat_lit 113443248) (nat_lit 14711657310) (nat_lit 0) A10K2.u6661 from rfl, totK_node, atot6660, atot6661]
  decide +kernel

theorem arows6665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6665 = true := by
  rw [show A10K2.u6665 = KTree.node A10K2.u6663 (nat_lit 113456365) (nat_lit 5437456470) (nat_lit 0) A10K2.u6664 from rfl, allE_node, arows6663, irow6665, arows6664]
  all_goals rfl

theorem atot6665 : totK PA10K2 A10K2.u6665 = [1293628547708, 5560736736446, 8072469291103, 4306291051596, 707506466119, 30311657555, 0, 0, 0, 0] := by
  rw [show A10K2.u6665 = KTree.node A10K2.u6663 (nat_lit 113456365) (nat_lit 5437456470) (nat_lit 0) A10K2.u6664 from rfl, totK_node, atot6663, atot6664]
  decide +kernel

theorem arows6670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6670 = true := by
  rw [show A10K2.u6670 = KTree.node A10K2.u6668 (nat_lit 113475168) (nat_lit 12486001397) (nat_lit 0) A10K2.u6669 from rfl, allE_node, arows6668, irow6670, arows6669]
  all_goals rfl

theorem atot6670 : totK PA10K2 A10K2.u6670 = [165731654200, 2488336616565, 7440878885346, 7397793289754, 2287151361230, 159639873615, 0, 0, 0, 0] := by
  rw [show A10K2.u6670 = KTree.node A10K2.u6668 (nat_lit 113475168) (nat_lit 12486001397) (nat_lit 0) A10K2.u6669 from rfl, totK_node, atot6668, atot6669]
  decide +kernel

theorem arows6673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6673 = true := by
  rw [show A10K2.u6673 = KTree.node A10K2.u6671 (nat_lit 113487550) (nat_lit 15916066347) (nat_lit 0) A10K2.u6672 from rfl, allE_node, arows6671, irow6673, arows6672]
  all_goals rfl

theorem atot6673 : totK PA10K2 A10K2.u6673 = [0, 1130290251433, 5305802703964, 8300202061674, 4522418294214, 640012949679, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u6673 = KTree.node A10K2.u6671 (nat_lit 113487550) (nat_lit 15916066347) (nat_lit 0) A10K2.u6672 from rfl, totK_node, atot6671, atot6672]
  decide +kernel

theorem arows6677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6677 = true := by
  rw [show A10K2.u6677 = KTree.node A10K2.u6675 (nat_lit 113507725) (nat_lit 3136726132) (nat_lit 0) A10K2.u6676 from rfl, allE_node, arows6675, irow6677, arows6676]
  all_goals rfl

theorem atot6677 : totK PA10K2 A10K2.u6677 = [0, 1174218341057, 5083263578315, 7645841348855, 4656751365211, 1007385664543, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u6677 = KTree.node A10K2.u6675 (nat_lit 113507725) (nat_lit 3136726132) (nat_lit 0) A10K2.u6676 from rfl, totK_node, atot6675, atot6676]
  decide +kernel

theorem arows6680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6680 = true := by
  rw [show A10K2.u6680 = KTree.node A10K2.u6678 (nat_lit 113525313) (nat_lit 10282547901) (nat_lit 0) A10K2.u6679 from rfl, allE_node, arows6678, irow6680, arows6679]
  all_goals rfl

theorem atot6680 : totK PA10K2 A10K2.u6680 = [0, 879991544888, 4609106986705, 7846557460091, 4673887616280, 810620116691, 36536693801, 0, 0, 0] := by
  rw [show A10K2.u6680 = KTree.node A10K2.u6678 (nat_lit 113525313) (nat_lit 10282547901) (nat_lit 0) A10K2.u6679 from rfl, totK_node, atot6678, atot6679]
  decide +kernel

theorem arows6686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6686 = true := by
  rw [show A10K2.u6686 = KTree.node A10K2.u6684 (nat_lit 113540101) (nat_lit 5311435891) (nat_lit 0) A10K2.u6685 from rfl, allE_node, arows6684, irow6686, arows6685]
  all_goals rfl

theorem atot6686 : totK PA10K2 A10K2.u6686 = [0, 504850548399, 3692350821757, 8102062892371, 6094972422512, 1294037683619, 66253585394, 0, 0, 0] := by
  rw [show A10K2.u6686 = KTree.node A10K2.u6684 (nat_lit 113540101) (nat_lit 5311435891) (nat_lit 0) A10K2.u6685 from rfl, totK_node, atot6684, atot6685]
  decide +kernel

theorem arows6689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6689 = true := by
  rw [show A10K2.u6689 = KTree.node A10K2.u6687 (nat_lit 113558089) (nat_lit 9565289491) (nat_lit 0) A10K2.u6688 from rfl, allE_node, arows6687, irow6689, arows6688]
  all_goals rfl

theorem atot6689 : totK PA10K2 A10K2.u6689 = [0, 0, 870828675635, 4651082116046, 7754814511407, 4357841608351, 772168195939, 36134558889, 0, 0] := by
  rw [show A10K2.u6689 = KTree.node A10K2.u6687 (nat_lit 113558089) (nat_lit 9565289491) (nat_lit 0) A10K2.u6688 from rfl, totK_node, atot6687, atot6688]
  decide +kernel

theorem arows6693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6693 = true := by
  rw [show A10K2.u6693 = KTree.node A10K2.u6691 (nat_lit 113642533) (nat_lit 6797344365) (nat_lit 0) A10K2.u6692 from rfl, allE_node, arows6691, irow6693, arows6692]
  all_goals rfl

theorem atot6693 : totK PA10K2 A10K2.u6693 = [0, 1035351872294, 4756815757816, 7644914302972, 5020642474653, 1129904399591, 74743123071, 0, 0, 0] := by
  rw [show A10K2.u6693 = KTree.node A10K2.u6691 (nat_lit 113642533) (nat_lit 6797344365) (nat_lit 0) A10K2.u6692 from rfl, totK_node, atot6691, atot6692]
  decide +kernel

theorem arows6696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6696 = true := by
  rw [show A10K2.u6696 = KTree.node A10K2.u6694 (nat_lit 113672749) (nat_lit 5533269284) (nat_lit 0) A10K2.u6695 from rfl, allE_node, arows6694, irow6696, arows6695]
  all_goals rfl

theorem atot6696 : totK PA10K2 A10K2.u6696 = [0, 282722822571, 3165894440601, 7977058133482, 6247851608102, 1346728021960, 69639688133, 0, 0, 0] := by
  rw [show A10K2.u6696 = KTree.node A10K2.u6694 (nat_lit 113672749) (nat_lit 5533269284) (nat_lit 0) A10K2.u6695 from rfl, totK_node, atot6694, atot6695]
  decide +kernel

theorem arows6701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6701 = true := by
  rw [show A10K2.u6701 = KTree.node A10K2.u6699 (nat_lit 113708183) (nat_lit 14069194827) (nat_lit 0) A10K2.u6700 from rfl, allE_node, arows6699, irow6701, arows6700]
  all_goals rfl

theorem atot6701 : totK PA10K2 A10K2.u6701 = [0, 1076662042106, 4492534112120, 6853536598376, 4992125534642, 1698568912634, 211344872461, 5676195732, 0, 0] := by
  rw [show A10K2.u6701 = KTree.node A10K2.u6699 (nat_lit 113708183) (nat_lit 14069194827) (nat_lit 0) A10K2.u6700 from rfl, totK_node, atot6699, atot6700]
  decide +kernel

theorem arows6704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6704 = true := by
  rw [show A10K2.u6704 = KTree.node A10K2.u6702 (nat_lit 113729996) (nat_lit 6698873614) (nat_lit 0) A10K2.u6703 from rfl, allE_node, arows6702, irow6704, arows6703]
  all_goals rfl

theorem atot6704 : totK PA10K2 A10K2.u6704 = [0, 1175525378015, 5438095701498, 8378132243088, 4479283374065, 640742524927, 14004528958, 0, 0, 0] := by
  rw [show A10K2.u6704 = KTree.node A10K2.u6702 (nat_lit 113729996) (nat_lit 6698873614) (nat_lit 0) A10K2.u6703 from rfl, totK_node, atot6702, atot6703]
  decide +kernel

theorem arows6708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6708 = true := by
  rw [show A10K2.u6708 = KTree.node A10K2.u6706 (nat_lit 113846532) (nat_lit 12963048811) (nat_lit 0) A10K2.u6707 from rfl, allE_node, arows6706, irow6708, arows6707]
  all_goals rfl

theorem atot6708 : totK PA10K2 A10K2.u6708 = [849876618421, 3667503488132, 5991905606281, 5187890878758, 2897752761089, 786632278653, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u6708 = KTree.node A10K2.u6706 (nat_lit 113846532) (nat_lit 12963048811) (nat_lit 0) A10K2.u6707 from rfl, totK_node, atot6706, atot6707]
  decide +kernel

theorem arows6711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6711 = true := by
  rw [show A10K2.u6711 = KTree.node A10K2.u6709 (nat_lit 113858722) (nat_lit 13872347607) (nat_lit 0) A10K2.u6710 from rfl, allE_node, arows6709, irow6711, arows6710]
  all_goals rfl

theorem atot6711 : totK PA10K2 A10K2.u6711 = [1388287699512, 5966286900866, 8139304921963, 3616705213678, 457935242492, 12388698189, 0, 0, 0, 0] := by
  rw [show A10K2.u6711 = KTree.node A10K2.u6709 (nat_lit 113858722) (nat_lit 13872347607) (nat_lit 0) A10K2.u6710 from rfl, totK_node, atot6709, atot6710]
  decide +kernel

theorem arows6718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6718 = true := by
  rw [show A10K2.u6718 = KTree.node A10K2.u6716 (nat_lit 113878739) (nat_lit 10734820796) (nat_lit 0) A10K2.u6717 from rfl, allE_node, arows6716, irow6718, arows6717]
  all_goals rfl

theorem atot6718 : totK PA10K2 A10K2.u6718 = [0, 1649294100692, 6423976362352, 7828664962044, 3211898708285, 472273051388, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u6718 = KTree.node A10K2.u6716 (nat_lit 113878739) (nat_lit 10734820796) (nat_lit 0) A10K2.u6717 from rfl, totK_node, atot6716, atot6717]
  decide +kernel

theorem arows6721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6721 = true := by
  rw [show A10K2.u6721 = KTree.node A10K2.u6719 (nat_lit 113890518) (nat_lit 13807230986) (nat_lit 0) A10K2.u6720 from rfl, allE_node, arows6719, irow6721, arows6720]
  all_goals rfl

theorem atot6721 : totK PA10K2 A10K2.u6721 = [0, 1386269820000, 5827697908300, 7899087409564, 3607335699481, 468083113445, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u6721 = KTree.node A10K2.u6719 (nat_lit 113890518) (nat_lit 13807230986) (nat_lit 0) A10K2.u6720 from rfl, totK_node, atot6719, atot6720]
  decide +kernel

theorem arows6725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6725 = true := by
  rw [show A10K2.u6725 = KTree.node A10K2.u6723 (nat_lit 113915155) (nat_lit 10823858322) (nat_lit 0) A10K2.u6724 from rfl, allE_node, arows6723, irow6725, arows6724]
  all_goals rfl

theorem atot6725 : totK PA10K2 A10K2.u6725 = [1323934157412, 5211500593760, 7348421575969, 4582258972121, 1160256251743, 82268358908, 0, 0, 0, 0] := by
  rw [show A10K2.u6725 = KTree.node A10K2.u6723 (nat_lit 113915155) (nat_lit 10823858322) (nat_lit 0) A10K2.u6724 from rfl, totK_node, atot6723, atot6724]
  decide +kernel

theorem arows6728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6728 = true := by
  rw [show A10K2.u6728 = KTree.node A10K2.u6726 (nat_lit 113945238) (nat_lit 12850190298) (nat_lit 0) A10K2.u6727 from rfl, allE_node, arows6726, irow6728, arows6727]
  all_goals rfl

theorem atot6728 : totK PA10K2 A10K2.u6728 = [0, 2267524261285, 7572691783452, 7376172196972, 1963154501656, 117661498282, 0, 0, 0, 0] := by
  rw [show A10K2.u6728 = KTree.node A10K2.u6726 (nat_lit 113945238) (nat_lit 12850190298) (nat_lit 0) A10K2.u6727 from rfl, totK_node, atot6726, atot6727]
  decide +kernel

theorem arows6733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6733 = true := by
  rw [show A10K2.u6733 = KTree.node A10K2.u6731 (nat_lit 113971748) (nat_lit 10959868321) (nat_lit 0) A10K2.u6732 from rfl, allE_node, arows6731, irow6733, arows6732]
  all_goals rfl

theorem atot6733 : totK PA10K2 A10K2.u6733 = [1384975343664, 5553257636921, 7371906751854, 4026797944338, 1225633253239, 217969968774, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6733 = KTree.node A10K2.u6731 (nat_lit 113971748) (nat_lit 10959868321) (nat_lit 0) A10K2.u6732 from rfl, totK_node, atot6731, atot6732]
  decide +kernel

theorem arows6736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6736 = true := by
  rw [show A10K2.u6736 = KTree.node A10K2.u6734 (nat_lit 113992869) (nat_lit 6114832039) (nat_lit 0) A10K2.u6735 from rfl, allE_node, arows6734, irow6736, arows6735]
  all_goals rfl

theorem atot6736 : totK PA10K2 A10K2.u6736 = [868650652504, 4647325234802, 8180279743970, 5182382911967, 957035531409, 38600540508, 0, 0, 0, 0] := by
  rw [show A10K2.u6736 = KTree.node A10K2.u6734 (nat_lit 113992869) (nat_lit 6114832039) (nat_lit 0) A10K2.u6735 from rfl, totK_node, atot6734, atot6735]
  decide +kernel

theorem arows6740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6740 = true := by
  rw [show A10K2.u6740 = KTree.node A10K2.u6738 (nat_lit 114003667) (nat_lit 9425201519) (nat_lit 0) A10K2.u6739 from rfl, allE_node, arows6738, irow6740, arows6739]
  all_goals rfl

theorem atot6740 : totK PA10K2 A10K2.u6740 = [0, 1440426309345, 6124129020946, 8248448629149, 3641035421565, 435582869119, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6740 = KTree.node A10K2.u6738 (nat_lit 114003667) (nat_lit 9425201519) (nat_lit 0) A10K2.u6739 from rfl, totK_node, atot6738, atot6739]
  decide +kernel

theorem arows6743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6743 = true := by
  rw [show A10K2.u6743 = KTree.node A10K2.u6741 (nat_lit 114025010) (nat_lit 10171640832) (nat_lit 0) A10K2.u6742 from rfl, allE_node, arows6741, irow6743, arows6742]
  all_goals rfl

theorem atot6743 : totK PA10K2 A10K2.u6743 = [0, 1137825479782, 5402059272802, 8298833691152, 4467222535973, 614142802663, 13113983930, 0, 0, 0] := by
  rw [show A10K2.u6743 = KTree.node A10K2.u6741 (nat_lit 114025010) (nat_lit 10171640832) (nat_lit 0) A10K2.u6742 from rfl, totK_node, atot6741, atot6742]
  decide +kernel

theorem arows6749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6749 = true := by
  rw [show A10K2.u6749 = KTree.node A10K2.u6747 (nat_lit 114108768) (nat_lit 11010595262) (nat_lit 0) A10K2.u6748 from rfl, allE_node, arows6747, irow6749, arows6748]
  all_goals rfl

theorem atot6749 : totK PA10K2 A10K2.u6749 = [0, 849389605546, 4228145470231, 7484769854634, 5352131615345, 1307221675584, 86811916481, 0, 0, 0] := by
  rw [show A10K2.u6749 = KTree.node A10K2.u6747 (nat_lit 114108768) (nat_lit 11010595262) (nat_lit 0) A10K2.u6748 from rfl, totK_node, atot6747, atot6748]
  decide +kernel

theorem arows6752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6752 = true := by
  rw [show A10K2.u6752 = KTree.node A10K2.u6750 (nat_lit 114120966) (nat_lit 17340992) (nat_lit 0) A10K2.u6751 from rfl, allE_node, arows6750, irow6752, arows6751]
  all_goals rfl

theorem atot6752 : totK PA10K2 A10K2.u6752 = [0, 1386819479308, 6003764321579, 8201077367570, 3599881112013, 388221522155, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6752 = KTree.node A10K2.u6750 (nat_lit 114120966) (nat_lit 17340992) (nat_lit 0) A10K2.u6751 from rfl, totK_node, atot6750, atot6751]
  decide +kernel

theorem arows6756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6756 = true := by
  rw [show A10K2.u6756 = KTree.node A10K2.u6754 (nat_lit 114141086) (nat_lit 15173828327) (nat_lit 0) A10K2.u6755 from rfl, allE_node, arows6754, irow6756, arows6755]
  all_goals rfl

theorem atot6756 : totK PA10K2 A10K2.u6756 = [0, 0, 1521957371916, 6224224498403, 7794028670322, 3246951938223, 486459331688, 25565504801, 0, 0] := by
  rw [show A10K2.u6756 = KTree.node A10K2.u6754 (nat_lit 114141086) (nat_lit 15173828327) (nat_lit 0) A10K2.u6755 from rfl, totK_node, atot6754, atot6755]
  decide +kernel

theorem arows6759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6759 = true := by
  rw [show A10K2.u6759 = KTree.node A10K2.u6757 (nat_lit 114153618) (nat_lit 15203200646) (nat_lit 0) A10K2.u6758 from rfl, allE_node, arows6757, irow6759, arows6758]
  all_goals rfl

theorem atot6759 : totK PA10K2 A10K2.u6759 = [0, 304922396905, 2041454899404, 5923430266910, 7284111365405, 3207682076488, 419796078602, 11138589073, 0, 0] := by
  rw [show A10K2.u6759 = KTree.node A10K2.u6757 (nat_lit 114153618) (nat_lit 15203200646) (nat_lit 0) A10K2.u6758 from rfl, totK_node, atot6757, atot6758]
  decide +kernel

theorem arows6764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6764 = true := by
  rw [show A10K2.u6764 = KTree.node A10K2.u6762 (nat_lit 114178272) (nat_lit 8240125711) (nat_lit 0) A10K2.u6763 from rfl, allE_node, arows6762, irow6764, arows6763]
  all_goals rfl

theorem atot6764 : totK PA10K2 A10K2.u6764 = [0, 1018544825537, 5249730244930, 8195967552747, 4353964472569, 699039847659, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6764 = KTree.node A10K2.u6762 (nat_lit 114178272) (nat_lit 8240125711) (nat_lit 0) A10K2.u6763 from rfl, totK_node, atot6762, atot6763]
  decide +kernel

theorem arows6767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6767 = true := by
  rw [show A10K2.u6767 = KTree.node A10K2.u6765 (nat_lit 114214065) (nat_lit 1482740956) (nat_lit 0) A10K2.u6766 from rfl, allE_node, arows6765, irow6767, arows6766]
  all_goals rfl

theorem atot6767 : totK PA10K2 A10K2.u6767 = [0, 187199794786, 1995765237952, 6530930646534, 7438366532374, 2565235919781, 274108767403, 6239673734, 0, 0] := by
  rw [show A10K2.u6767 = KTree.node A10K2.u6765 (nat_lit 114214065) (nat_lit 1482740956) (nat_lit 0) A10K2.u6766 from rfl, totK_node, atot6765, atot6766]
  decide +kernel

theorem arows6771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6771 = true := by
  rw [show A10K2.u6771 = KTree.node A10K2.u6769 (nat_lit 114238756) (nat_lit 13453642002) (nat_lit 0) A10K2.u6770 from rfl, allE_node, arows6769, irow6771, arows6770]
  all_goals rfl

theorem atot6771 : totK PA10K2 A10K2.u6771 = [0, 1197284887858, 5507010967328, 8229750053927, 4336740720426, 694645057986, 27336624914, 0, 0, 0] := by
  rw [show A10K2.u6771 = KTree.node A10K2.u6769 (nat_lit 114238756) (nat_lit 13453642002) (nat_lit 0) A10K2.u6770 from rfl, totK_node, atot6769, atot6770]
  decide +kernel

theorem arows6774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6774 = true := by
  rw [show A10K2.u6774 = KTree.node A10K2.u6772 (nat_lit 114257106) (nat_lit 15415996847) (nat_lit 0) A10K2.u6773 from rfl, allE_node, arows6772, irow6774, arows6773]
  all_goals rfl

theorem atot6774 : totK PA10K2 A10K2.u6774 = [0, 868159679083, 4542728184571, 8139360082150, 5389267906235, 1005076815556, 30051286111, 0, 0, 0] := by
  rw [show A10K2.u6774 = KTree.node A10K2.u6772 (nat_lit 114257106) (nat_lit 15415996847) (nat_lit 0) A10K2.u6773 from rfl, totK_node, atot6772, atot6773]
  decide +kernel

theorem arows6782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6782 = true := by
  rw [show A10K2.u6782 = KTree.node A10K2.u6780 (nat_lit 114823268) (nat_lit 12580443690) (nat_lit 0) A10K2.u6781 from rfl, allE_node, arows6780, irow6782, arows6781]
  all_goals rfl

theorem atot6782 : totK PA10K2 A10K2.u6782 = [1248907596099, 5190600054857, 7187759554244, 3939069435057, 1162630824229, 367936110487, 43287591117, 0, 0, 0] := by
  rw [show A10K2.u6782 = KTree.node A10K2.u6780 (nat_lit 114823268) (nat_lit 12580443690) (nat_lit 0) A10K2.u6781 from rfl, totK_node, atot6780, atot6781]
  decide +kernel

theorem arows6785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6785 = true := by
  rw [show A10K2.u6785 = KTree.node A10K2.u6783 (nat_lit 114847118) (nat_lit 15185175319) (nat_lit 0) A10K2.u6784 from rfl, allE_node, arows6783, irow6785, arows6784]
  all_goals rfl

theorem atot6785 : totK PA10K2 A10K2.u6785 = [832063008302, 4499161558591, 8184964910100, 5461372651641, 1077028452027, 32019442958, 0, 0, 0, 0] := by
  rw [show A10K2.u6785 = KTree.node A10K2.u6783 (nat_lit 114847118) (nat_lit 15185175319) (nat_lit 0) A10K2.u6784 from rfl, totK_node, atot6783, atot6784]
  decide +kernel

theorem arows6789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6789 = true := by
  rw [show A10K2.u6789 = KTree.node A10K2.u6787 (nat_lit 114856382) (nat_lit 16006129379) (nat_lit 0) A10K2.u6788 from rfl, allE_node, arows6787, irow6789, arows6788]
  all_goals rfl

theorem atot6789 : totK PA10K2 A10K2.u6789 = [0, 1246176484060, 5442120513077, 7646522705659, 3821473391351, 657483398518, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6789 = KTree.node A10K2.u6787 (nat_lit 114856382) (nat_lit 16006129379) (nat_lit 0) A10K2.u6788 from rfl, totK_node, atot6787, atot6788]
  decide +kernel

theorem arows6792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6792 = true := by
  rw [show A10K2.u6792 = KTree.node A10K2.u6790 (nat_lit 114880226) (nat_lit 10788522490) (nat_lit 0) A10K2.u6791 from rfl, allE_node, arows6790, irow6792, arows6791]
  all_goals rfl

theorem atot6792 : totK PA10K2 A10K2.u6792 = [811040046021, 3975451144464, 7029818652181, 5713015108125, 1970574758837, 223850327454, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6792 = KTree.node A10K2.u6790 (nat_lit 114880226) (nat_lit 10788522490) (nat_lit 0) A10K2.u6791 from rfl, totK_node, atot6790, atot6791]
  decide +kernel

theorem arows6797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6797 = true := by
  rw [show A10K2.u6797 = KTree.node A10K2.u6795 (nat_lit 114903715) (nat_lit 10414015437) (nat_lit 0) A10K2.u6796 from rfl, allE_node, arows6795, irow6797, arows6796]
  all_goals rfl

theorem atot6797 : totK PA10K2 A10K2.u6797 = [1277311426415, 5286519845816, 7735312150030, 4318370167932, 795194687735, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u6797 = KTree.node A10K2.u6795 (nat_lit 114903715) (nat_lit 10414015437) (nat_lit 0) A10K2.u6796 from rfl, totK_node, atot6795, atot6796]
  decide +kernel

theorem arows6800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6800 = true := by
  rw [show A10K2.u6800 = KTree.node A10K2.u6798 (nat_lit 114917342) (nat_lit 14795252321) (nat_lit 0) A10K2.u6799 from rfl, allE_node, arows6798, irow6800, arows6799]
  all_goals rfl

theorem atot6800 : totK PA10K2 A10K2.u6800 = [0, 2111303627107, 7392077006374, 7816195549749, 2422003734213, 157256452208, 0, 0, 0, 0] := by
  rw [show A10K2.u6800 = KTree.node A10K2.u6798 (nat_lit 114917342) (nat_lit 14795252321) (nat_lit 0) A10K2.u6799 from rfl, totK_node, atot6798, atot6799]
  decide +kernel

theorem arows6804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6804 = true := by
  rw [show A10K2.u6804 = KTree.node A10K2.u6802 (nat_lit 114939107) (nat_lit 10422362033) (nat_lit 0) A10K2.u6803 from rfl, allE_node, arows6802, irow6804, arows6803]
  all_goals rfl

theorem atot6804 : totK PA10K2 A10K2.u6804 = [0, 1275984678170, 5489746111349, 7732898427915, 4045578112432, 739272430033, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6804 = KTree.node A10K2.u6802 (nat_lit 114939107) (nat_lit 10422362033) (nat_lit 0) A10K2.u6803 from rfl, totK_node, atot6802, atot6803]
  decide +kernel

theorem arows6807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6807 = true := by
  rw [show A10K2.u6807 = KTree.node A10K2.u6805 (nat_lit 115020165) (nat_lit 5285558703) (nat_lit 0) A10K2.u6806 from rfl, allE_node, arows6805, irow6807, arows6806]
  all_goals rfl

theorem atot6807 : totK PA10K2 A10K2.u6807 = [1300028584640, 5419682528411, 7539342416974, 4155686828290, 967838379205, 74314089354, 0, 0, 0, 0] := by
  rw [show A10K2.u6807 = KTree.node A10K2.u6805 (nat_lit 115020165) (nat_lit 5285558703) (nat_lit 0) A10K2.u6806 from rfl, totK_node, atot6805, atot6806]
  decide +kernel

theorem arows6813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6813 = true := by
  rw [show A10K2.u6813 = KTree.node A10K2.u6811 (nat_lit 115040582) (nat_lit 11785411376) (nat_lit 0) A10K2.u6812 from rfl, allE_node, arows6811, irow6813, arows6812]
  all_goals rfl

theorem atot6813 : totK PA10K2 A10K2.u6813 = [1124207821172, 5287935376850, 8240278755489, 4548691077357, 735005306207, 30428024596, 0, 0, 0, 0] := by
  rw [show A10K2.u6813 = KTree.node A10K2.u6811 (nat_lit 115040582) (nat_lit 11785411376) (nat_lit 0) A10K2.u6812 from rfl, totK_node, atot6811, atot6812]
  decide +kernel

theorem arows6816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6816 = true := by
  rw [show A10K2.u6816 = KTree.node A10K2.u6814 (nat_lit 115049374) (nat_lit 14723083452) (nat_lit 0) A10K2.u6815 from rfl, allE_node, arows6814, irow6816, arows6815]
  all_goals rfl

theorem atot6816 : totK PA10K2 A10K2.u6816 = [0, 1373773664602, 6037092780713, 8296821676408, 3578630227817, 395289441793, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6816 = KTree.node A10K2.u6814 (nat_lit 115049374) (nat_lit 14723083452) (nat_lit 0) A10K2.u6815 from rfl, totK_node, atot6814, atot6815]
  decide +kernel

theorem arows6820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6820 = true := by
  rw [show A10K2.u6820 = KTree.node A10K2.u6818 (nat_lit 115062450) (nat_lit 15127922656) (nat_lit 0) A10K2.u6819 from rfl, allE_node, arows6818, irow6820, arows6819]
  all_goals rfl

theorem atot6820 : totK PA10K2 A10K2.u6820 = [0, 1642718947138, 6333456382110, 7909501084933, 3460641600280, 413060525080, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6820 = KTree.node A10K2.u6818 (nat_lit 115062450) (nat_lit 15127922656) (nat_lit 0) A10K2.u6819 from rfl, totK_node, atot6818, atot6819]
  decide +kernel

theorem arows6823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6823 = true := by
  rw [show A10K2.u6823 = KTree.node A10K2.u6821 (nat_lit 115081108) (nat_lit 6002962782) (nat_lit 0) A10K2.u6822 from rfl, allE_node, arows6821, irow6823, arows6822]
  all_goals rfl

theorem atot6823 : totK PA10K2 A10K2.u6823 = [0, 824100700022, 4543345413095, 7966333414241, 5135184942101, 1071614930130, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u6823 = KTree.node A10K2.u6821 (nat_lit 115081108) (nat_lit 6002962782) (nat_lit 0) A10K2.u6822 from rfl, totK_node, atot6821, atot6822]
  decide +kernel

theorem arows6828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6828 = true := by
  rw [show A10K2.u6828 = KTree.node A10K2.u6826 (nat_lit 115100456) (nat_lit 11557315889) (nat_lit 0) A10K2.u6827 from rfl, allE_node, arows6826, irow6828, arows6827]
  all_goals rfl

theorem atot6828 : totK PA10K2 A10K2.u6828 = [0, 1272047147352, 5377322241410, 7724996086967, 4134003341123, 754130907206, 36485460093, 0, 0, 0] := by
  rw [show A10K2.u6828 = KTree.node A10K2.u6826 (nat_lit 115100456) (nat_lit 11557315889) (nat_lit 0) A10K2.u6827 from rfl, totK_node, atot6826, atot6827]
  decide +kernel

theorem arows6831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6831 = true := by
  rw [show A10K2.u6831 = KTree.node A10K2.u6829 (nat_lit 115114035) (nat_lit 4796067285) (nat_lit 0) A10K2.u6830 from rfl, allE_node, arows6829, irow6831, arows6830]
  all_goals rfl

theorem atot6831 : totK PA10K2 A10K2.u6831 = [0, 0, 1953297896338, 7117377194614, 7842382896699, 2615340930258, 224353091571, 0, 0, 0] := by
  rw [show A10K2.u6831 = KTree.node A10K2.u6829 (nat_lit 115114035) (nat_lit 4796067285) (nat_lit 0) A10K2.u6830 from rfl, totK_node, atot6829, atot6830]
  decide +kernel

theorem arows6835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6835 = true := by
  rw [show A10K2.u6835 = KTree.node A10K2.u6833 (nat_lit 115139734) (nat_lit 15069123615) (nat_lit 0) A10K2.u6834 from rfl, allE_node, arows6833, irow6835, arows6834]
  all_goals rfl

theorem atot6835 : totK PA10K2 A10K2.u6835 = [0, 513260446086, 3038026814888, 6778704341120, 6584630611236, 2257514434524, 236791261068, 7007974415, 0, 0] := by
  rw [show A10K2.u6835 = KTree.node A10K2.u6833 (nat_lit 115139734) (nat_lit 15069123615) (nat_lit 0) A10K2.u6834 from rfl, totK_node, atot6833, atot6834]
  decide +kernel

theorem arows6838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6838 = true := by
  rw [show A10K2.u6838 = KTree.node A10K2.u6836 (nat_lit 115162516) (nat_lit 8089826329) (nat_lit 0) A10K2.u6837 from rfl, allE_node, arows6836, irow6838, arows6837]
  all_goals rfl

theorem atot6838 : totK PA10K2 A10K2.u6838 = [0, 959330459403, 4815886189084, 8038333745989, 4707367164421, 832847388529, 37546598172, 0, 0, 0] := by
  rw [show A10K2.u6838 = KTree.node A10K2.u6836 (nat_lit 115162516) (nat_lit 8089826329) (nat_lit 0) A10K2.u6837 from rfl, totK_node, atot6836, atot6837]
  decide +kernel

theorem arows6845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6845 = true := by
  rw [show A10K2.u6845 = KTree.node A10K2.u6843 (nat_lit 115176918) (nat_lit 15723628633) (nat_lit 0) A10K2.u6844 from rfl, allE_node, arows6843, irow6845, arows6844]
  all_goals rfl

theorem atot6845 : totK PA10K2 A10K2.u6845 = [0, 613762948205, 3714312183298, 7738266724396, 6212367907735, 1576604597758, 94106083090, 0, 0, 0] := by
  rw [show A10K2.u6845 = KTree.node A10K2.u6843 (nat_lit 115176918) (nat_lit 15723628633) (nat_lit 0) A10K2.u6844 from rfl, totK_node, atot6843, atot6844]
  decide +kernel

theorem arows6848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6848 = true := by
  rw [show A10K2.u6848 = KTree.node A10K2.u6846 (nat_lit 115198181) (nat_lit 7160463942) (nat_lit 0) A10K2.u6847 from rfl, allE_node, arows6846, irow6848, arows6847]
  all_goals rfl

theorem atot6848 : totK PA10K2 A10K2.u6848 = [0, 128889292512, 1799520742558, 6297599985531, 7885885571490, 3306687021587, 379116771022, 7151180950, 0, 0] := by
  rw [show A10K2.u6848 = KTree.node A10K2.u6846 (nat_lit 115198181) (nat_lit 7160463942) (nat_lit 0) A10K2.u6847 from rfl, totK_node, atot6846, atot6847]
  decide +kernel

theorem arows6852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6852 = true := by
  rw [show A10K2.u6852 = KTree.node A10K2.u6850 (nat_lit 115283968) (nat_lit 15368788893) (nat_lit 0) A10K2.u6851 from rfl, allE_node, arows6850, irow6852, arows6851]
  all_goals rfl

theorem atot6852 : totK PA10K2 A10K2.u6852 = [0, 1397910930241, 5930284249040, 7994729916157, 3764957127933, 528113898928, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u6852 = KTree.node A10K2.u6850 (nat_lit 115283968) (nat_lit 15368788893) (nat_lit 0) A10K2.u6851 from rfl, totK_node, atot6850, atot6851]
  decide +kernel

theorem arows6855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6855 = true := by
  rw [show A10K2.u6855 = KTree.node A10K2.u6853 (nat_lit 115303645) (nat_lit 5437315270) (nat_lit 0) A10K2.u6854 from rfl, allE_node, arows6853, irow6855, arows6854]
  all_goals rfl

theorem atot6855 : totK PA10K2 A10K2.u6855 = [0, 894451438357, 4729678133052, 8300272600018, 5133161178152, 793931935011, 18992036149, 0, 0, 0] := by
  rw [show A10K2.u6855 = KTree.node A10K2.u6853 (nat_lit 115303645) (nat_lit 5437315270) (nat_lit 0) A10K2.u6854 from rfl, totK_node, atot6853, atot6854]
  decide +kernel

theorem arows6860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6860 = true := by
  rw [show A10K2.u6860 = KTree.node A10K2.u6858 (nat_lit 115314104) (nat_lit 14312206078) (nat_lit 0) A10K2.u6859 from rfl, allE_node, arows6858, irow6860, arows6859]
  all_goals rfl

theorem atot6860 : totK PA10K2 A10K2.u6860 = [0, 0, 1453932899181, 6121470135513, 8269973155270, 3470580202725, 352929604409, 6318667960, 0, 0] := by
  rw [show A10K2.u6860 = KTree.node A10K2.u6858 (nat_lit 115314104) (nat_lit 14312206078) (nat_lit 0) A10K2.u6859 from rfl, totK_node, atot6858, atot6859]
  decide +kernel

theorem arows6863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6863 = true := by
  rw [show A10K2.u6863 = KTree.node A10K2.u6861 (nat_lit 115335603) (nat_lit 8236344417) (nat_lit 0) A10K2.u6862 from rfl, allE_node, arows6861, irow6863, arows6862]
  all_goals rfl

theorem atot6863 : totK PA10K2 A10K2.u6863 = [0, 0, 1282692887952, 5792676711802, 8197417419118, 3946776654371, 499543058554, 12460675034, 0, 0] := by
  rw [show A10K2.u6863 = KTree.node A10K2.u6861 (nat_lit 115335603) (nat_lit 8236344417) (nat_lit 0) A10K2.u6862 from rfl, totK_node, atot6861, atot6862]
  decide +kernel

theorem arows6867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6867 = true := by
  rw [show A10K2.u6867 = KTree.node A10K2.u6865 (nat_lit 115345570) (nat_lit 4053047282) (nat_lit 0) A10K2.u6866 from rfl, allE_node, arows6865, irow6867, arows6866]
  all_goals rfl

theorem atot6867 : totK PA10K2 A10K2.u6867 = [0, 846984141050, 3644876751420, 5910561257716, 5066602721053, 2938444302967, 786278497806, 54997142734, 0, 0] := by
  rw [show A10K2.u6867 = KTree.node A10K2.u6865 (nat_lit 115345570) (nat_lit 4053047282) (nat_lit 0) A10K2.u6866 from rfl, totK_node, atot6865, atot6866]
  decide +kernel

theorem arows6870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6870 = true := by
  rw [show A10K2.u6870 = KTree.node A10K2.u6868 (nat_lit 115365932) (nat_lit 13155048199) (nat_lit 0) A10K2.u6869 from rfl, allE_node, arows6868, irow6870, arows6869]
  all_goals rfl

theorem atot6870 : totK PA10K2 A10K2.u6870 = [0, 1384842093287, 5936939424174, 8063544847664, 3560513929481, 429340187680, 11436914703, 0, 0, 0] := by
  rw [show A10K2.u6870 = KTree.node A10K2.u6868 (nat_lit 115365932) (nat_lit 13155048199) (nat_lit 0) A10K2.u6869 from rfl, totK_node, atot6868, atot6869]
  decide +kernel

theorem arows6876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6876 = true := by
  rw [show A10K2.u6876 = KTree.node A10K2.u6874 (nat_lit 115376680) (nat_lit 12653131156) (nat_lit 0) A10K2.u6875 from rfl, allE_node, arows6874, irow6876, arows6875]
  all_goals rfl

theorem atot6876 : totK PA10K2 A10K2.u6876 = [0, 0, 1645333531088, 6479992102157, 7879675159569, 3106970041944, 462661044613, 25239774317, 0, 0] := by
  rw [show A10K2.u6876 = KTree.node A10K2.u6874 (nat_lit 115376680) (nat_lit 12653131156) (nat_lit 0) A10K2.u6875 from rfl, totK_node, atot6874, atot6875]
  decide +kernel

theorem arows6879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6879 = true := by
  rw [show A10K2.u6879 = KTree.node A10K2.u6877 (nat_lit 115396896) (nat_lit 13375405213) (nat_lit 0) A10K2.u6878 from rfl, allE_node, arows6877, irow6879, arows6878]
  all_goals rfl

theorem atot6879 : totK PA10K2 A10K2.u6879 = [0, 0, 1380949466044, 5827148293950, 7826827132635, 3458066077099, 443163400364, 10957026886, 0, 0] := by
  rw [show A10K2.u6879 = KTree.node A10K2.u6877 (nat_lit 115396896) (nat_lit 13375405213) (nat_lit 0) A10K2.u6878 from rfl, totK_node, atot6877, atot6878]
  decide +kernel

theorem arows6883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6883 = true := by
  rw [show A10K2.u6883 = KTree.node A10K2.u6881 (nat_lit 115478884) (nat_lit 13491273839) (nat_lit 0) A10K2.u6882 from rfl, allE_node, arows6881, irow6883, arows6882]
  all_goals rfl

theorem atot6883 : totK PA10K2 A10K2.u6883 = [0, 1318949507170, 5379954438081, 7437939454195, 4244434853919, 1009135356465, 74541061259, 0, 0, 0] := by
  rw [show A10K2.u6883 = KTree.node A10K2.u6881 (nat_lit 115478884) (nat_lit 13491273839) (nat_lit 0) A10K2.u6882 from rfl, totK_node, atot6881, atot6882]
  decide +kernel

theorem arows6886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6886 = true := by
  rw [show A10K2.u6886 = KTree.node A10K2.u6884 (nat_lit 115510053) (nat_lit 7447528903) (nat_lit 0) A10K2.u6885 from rfl, allE_node, arows6884, irow6886, arows6885]
  all_goals rfl

theorem atot6886 : totK PA10K2 A10K2.u6886 = [0, 0, 2053932941834, 7404268767715, 7498774676159, 2001560271551, 127030658961, 0, 0, 0] := by
  rw [show A10K2.u6886 = KTree.node A10K2.u6884 (nat_lit 115510053) (nat_lit 7447528903) (nat_lit 0) A10K2.u6885 from rfl, totK_node, atot6884, atot6885]
  decide +kernel

theorem arows6891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6891 = true := by
  rw [show A10K2.u6891 = KTree.node A10K2.u6889 (nat_lit 115544140) (nat_lit 10667708186) (nat_lit 0) A10K2.u6890 from rfl, allE_node, arows6889, irow6891, arows6890]
  all_goals rfl

theorem atot6891 : totK PA10K2 A10K2.u6891 = [0, 1383970300284, 5397580182577, 7272714013425, 4140942639604, 1175308181396, 160435084447, 5976421810, 0, 0] := by
  rw [show A10K2.u6891 = KTree.node A10K2.u6889 (nat_lit 115544140) (nat_lit 10667708186) (nat_lit 0) A10K2.u6890 from rfl, totK_node, atot6889, atot6890]
  decide +kernel

theorem arows6894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6894 = true := by
  rw [show A10K2.u6894 = KTree.node A10K2.u6892 (nat_lit 115565910) (nat_lit 11886913796) (nat_lit 0) A10K2.u6893 from rfl, allE_node, arows6892, irow6894, arows6893]
  all_goals rfl

theorem atot6894 : totK PA10K2 A10K2.u6894 = [0, 868494622419, 4774209875764, 8331464393393, 5120141340353, 919436040958, 26497647239, 0, 0, 0] := by
  rw [show A10K2.u6894 = KTree.node A10K2.u6892 (nat_lit 115565910) (nat_lit 11886913796) (nat_lit 0) A10K2.u6893 from rfl, totK_node, atot6892, atot6893]
  decide +kernel

theorem arows6898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6898 = true := by
  rw [show A10K2.u6898 = KTree.node A10K2.u6896 (nat_lit 115576260) (nat_lit 7794905996) (nat_lit 0) A10K2.u6897 from rfl, allE_node, arows6896, irow6898, arows6897]
  all_goals rfl

theorem atot6898 : totK PA10K2 A10K2.u6898 = [0, 0, 1402884912892, 6016063980886, 8219932807444, 3668029037374, 428973877227, 6904928264, 0, 0] := by
  rw [show A10K2.u6898 = KTree.node A10K2.u6896 (nat_lit 115576260) (nat_lit 7794905996) (nat_lit 0) A10K2.u6897 from rfl, totK_node, atot6896, atot6897]
  decide +kernel

theorem arows6901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6901 = true := by
  rw [show A10K2.u6901 = KTree.node A10K2.u6899 (nat_lit 115598230) (nat_lit 15858125233) (nat_lit 0) A10K2.u6900 from rfl, allE_node, arows6899, irow6901, arows6900]
  all_goals rfl

theorem atot6901 : totK PA10K2 A10K2.u6901 = [0, 0, 1174087269989, 5430189156097, 8305660554886, 4466904707430, 565945570593, 12833313880, 0, 0] := by
  rw [show A10K2.u6901 = KTree.node A10K2.u6899 (nat_lit 115598230) (nat_lit 15858125233) (nat_lit 0) A10K2.u6900 from rfl, totK_node, atot6899, atot6900]
  decide +kernel

theorem arows6910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6910 = true := by
  rw [show A10K2.u6910 = KTree.node A10K2.u6908 (nat_lit 115608403) (nat_lit 3409699472) (nat_lit 0) A10K2.u6909 from rfl, allE_node, arows6908, irow6910, arows6909]
  all_goals rfl

theorem atot6910 : totK PA10K2 A10K2.u6910 = [0, 0, 846984141050, 4252634405346, 7496073019486, 5217740976503, 1284805549000, 85874841514, 0, 0] := by
  rw [show A10K2.u6910 = KTree.node A10K2.u6908 (nat_lit 115608403) (nat_lit 3409699472) (nat_lit 0) A10K2.u6909 from rfl, totK_node, atot6908, atot6909]
  decide +kernel

theorem arows6913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6913 = true := by
  rw [show A10K2.u6913 = KTree.node A10K2.u6911 (nat_lit 115628826) (nat_lit 7752370208) (nat_lit 0) A10K2.u6912 from rfl, allE_node, arows6911, irow6913, arows6912]
  all_goals rfl

theorem atot6913 : totK PA10K2 A10K2.u6913 = [0, 0, 1384842093287, 5932994875750, 8062438255573, 3533549933255, 384677235867, 5705019915, 0, 0] := by
  rw [show A10K2.u6913 = KTree.node A10K2.u6911 (nat_lit 115628826) (nat_lit 7752370208) (nat_lit 0) A10K2.u6912 from rfl, totK_node, atot6911, atot6912]
  decide +kernel

theorem arows6917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6917 = true := by
  rw [show A10K2.u6917 = KTree.node A10K2.u6915 (nat_lit 115640876) (nat_lit 12570484968) (nat_lit 0) A10K2.u6916 from rfl, allE_node, arows6915, irow6917, arows6916]
  all_goals rfl

theorem atot6917 : totK PA10K2 A10K2.u6917 = [0, 0, 0, 1580582154124, 6350746625871, 7824908339475, 3068457669627, 371032613200, 7237400819, 0] := by
  rw [show A10K2.u6917 = KTree.node A10K2.u6915 (nat_lit 115640876) (nat_lit 12570484968) (nat_lit 0) A10K2.u6916 from rfl, totK_node, atot6915, atot6916]
  decide +kernel

theorem arows6920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6920 = true := by
  rw [show A10K2.u6920 = KTree.node A10K2.u6918 (nat_lit 115666609) (nat_lit 6218279453) (nat_lit 0) A10K2.u6919 from rfl, allE_node, arows6918, irow6920, arows6919]
  all_goals rfl

theorem atot6920 : totK PA10K2 A10K2.u6920 = [0, 0, 759378239577, 4258390595265, 7880104777875, 5423539732211, 1124642522976, 58036478655, 0, 0] := by
  rw [show A10K2.u6920 = KTree.node A10K2.u6918 (nat_lit 115666609) (nat_lit 6218279453) (nat_lit 0) A10K2.u6919 from rfl, totK_node, atot6918, atot6919]
  decide +kernel

theorem arows6925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6925 = true := by
  rw [show A10K2.u6925 = KTree.node A10K2.u6923 (nat_lit 115759146) (nat_lit 8953167437) (nat_lit 0) A10K2.u6924 from rfl, allE_node, arows6923, irow6925, arows6924]
  all_goals rfl

theorem atot6925 : totK PA10K2 A10K2.u6925 = [0, 0, 1351801176083, 5806024197938, 7973633054594, 3490348452728, 433376000901, 11814975521, 0, 0] := by
  rw [show A10K2.u6925 = KTree.node A10K2.u6923 (nat_lit 115759146) (nat_lit 8953167437) (nat_lit 0) A10K2.u6924 from rfl, totK_node, atot6923, atot6924]
  decide +kernel

theorem arows6928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6928 = true := by
  rw [show A10K2.u6928 = KTree.node A10K2.u6926 (nat_lit 115813789) (nat_lit 4150812180) (nat_lit 0) A10K2.u6927 from rfl, allE_node, arows6926, irow6928, arows6927]
  all_goals rfl

theorem atot6928 : totK PA10K2 A10K2.u6928 = [0, 0, 1131345380294, 5193324921792, 8176835046536, 4682689184449, 719968862699, 19333452023, 0, 0] := by
  rw [show A10K2.u6928 = KTree.node A10K2.u6926 (nat_lit 115813789) (nat_lit 4150812180) (nat_lit 0) A10K2.u6927 from rfl, totK_node, atot6926, atot6927]
  decide +kernel

theorem arows6932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6932 = true := by
  rw [show A10K2.u6932 = KTree.node A10K2.u6930 (nat_lit 115833892) (nat_lit 7275614612) (nat_lit 0) A10K2.u6931 from rfl, allE_node, arows6930, irow6932, arows6931]
  all_goals rfl

theorem atot6932 : totK PA10K2 A10K2.u6932 = [0, 765706699962, 2890632271249, 4835730137552, 5932015037285, 4173757581136, 1016869438216, 62368562949, 0, 0] := by
  rw [show A10K2.u6932 = KTree.node A10K2.u6930 (nat_lit 115833892) (nat_lit 7275614612) (nat_lit 0) A10K2.u6931 from rfl, totK_node, atot6930, atot6931]
  decide +kernel

theorem arows6935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6935 = true := by
  rw [show A10K2.u6935 = KTree.node A10K2.u6933 (nat_lit 115950750) (nat_lit 13985280109) (nat_lit 0) A10K2.u6934 from rfl, allE_node, arows6933, irow6935, arows6934]
  all_goals rfl

theorem atot6935 : totK PA10K2 A10K2.u6935 = [0, 844031696656, 4458665712326, 7954104948511, 4953987361287, 870947804251, 37750801259, 0, 0, 0] := by
  rw [show A10K2.u6935 = KTree.node A10K2.u6933 (nat_lit 115950750) (nat_lit 13985280109) (nat_lit 0) A10K2.u6934 from rfl, totK_node, atot6933, atot6934]
  decide +kernel

theorem arows6941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6941 = true := by
  rw [show A10K2.u6941 = KTree.node A10K2.u6939 (nat_lit 115963170) (nat_lit 13664070545) (nat_lit 0) A10K2.u6940 from rfl, allE_node, arows6939, irow6941, arows6940]
  all_goals rfl

theorem atot6941 : totK PA10K2 A10K2.u6941 = [0, 613166546329, 3952583216630, 7933942488282, 5917623611709, 1474515703345, 89124035270, 0, 0, 0] := by
  rw [show A10K2.u6941 = KTree.node A10K2.u6939 (nat_lit 115963170) (nat_lit 13664070545) (nat_lit 0) A10K2.u6940 from rfl, totK_node, atot6939, atot6940]
  decide +kernel

theorem arows6944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6944 = true := by
  rw [show A10K2.u6944 = KTree.node A10K2.u6942 (nat_lit 115981534) (nat_lit 11350878210) (nat_lit 0) A10K2.u6943 from rfl, allE_node, arows6942, irow6944, arows6943]
  all_goals rfl

theorem atot6944 : totK PA10K2 A10K2.u6944 = [0, 0, 876630763801, 4819142498460, 8127688796698, 4349826919484, 686305570555, 31082886609, 0, 0] := by
  rw [show A10K2.u6944 = KTree.node A10K2.u6942 (nat_lit 115981534) (nat_lit 11350878210) (nat_lit 0) A10K2.u6943 from rfl, totK_node, atot6942, atot6943]
  decide +kernel

theorem arows6948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6948 = true := by
  rw [show A10K2.u6948 = KTree.node A10K2.u6946 (nat_lit 116008288) (nat_lit 9729420434) (nat_lit 0) A10K2.u6947 from rfl, allE_node, arows6946, irow6948, arows6947]
  all_goals rfl

theorem atot6948 : totK PA10K2 A10K2.u6948 = [0, 762716802215, 3975652214628, 7254548097658, 5710489390765, 1899723789428, 231373924561, 5885702948, 0, 0] := by
  rw [show A10K2.u6948 = KTree.node A10K2.u6946 (nat_lit 116008288) (nat_lit 9729420434) (nat_lit 0) A10K2.u6947 from rfl, totK_node, atot6946, atot6947]
  decide +kernel

theorem arows6951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6951 = true := by
  rw [show A10K2.u6951 = KTree.node A10K2.u6949 (nat_lit 116020671) (nat_lit 13062454596) (nat_lit 0) A10K2.u6950 from rfl, allE_node, arows6949, irow6951, arows6950]
  all_goals rfl

theorem atot6951 : totK PA10K2 A10K2.u6951 = [0, 561217355197, 3747042337462, 7908566911535, 5928436378017, 1218672377225, 51508016309, 0, 0, 0] := by
  rw [show A10K2.u6951 = KTree.node A10K2.u6949 (nat_lit 116020671) (nat_lit 13062454596) (nat_lit 0) A10K2.u6950 from rfl, totK_node, atot6949, atot6950]
  decide +kernel

theorem arows6956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6956 = true := by
  rw [show A10K2.u6956 = KTree.node A10K2.u6954 (nat_lit 116064370) (nat_lit 9658301811) (nat_lit 0) A10K2.u6955 from rfl, allE_node, arows6954, irow6956, arows6955]
  all_goals rfl

theorem atot6956 : totK PA10K2 A10K2.u6956 = [0, 664048194155, 3432854806658, 6929577361382, 6167964098215, 2061181281045, 240781649186, 6354482628, 0, 0] := by
  rw [show A10K2.u6956 = KTree.node A10K2.u6954 (nat_lit 116064370) (nat_lit 9658301811) (nat_lit 0) A10K2.u6955 from rfl, totK_node, atot6954, atot6955]
  decide +kernel

theorem arows6959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6959 = true := by
  rw [show A10K2.u6959 = KTree.node A10K2.u6957 (nat_lit 116078290) (nat_lit 15271571326) (nat_lit 0) A10K2.u6958 from rfl, allE_node, arows6957, irow6959, arows6958]
  all_goals rfl

theorem atot6959 : totK PA10K2 A10K2.u6959 = [0, 1333248599601, 5679552489103, 7962464109908, 4053013176834, 682664392909, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u6959 = KTree.node A10K2.u6957 (nat_lit 116078290) (nat_lit 15271571326) (nat_lit 0) A10K2.u6958 from rfl, totK_node, atot6957, atot6958]
  decide +kernel

theorem arows6963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6963 = true := by
  rw [show A10K2.u6963 = KTree.node A10K2.u6961 (nat_lit 116096478) (nat_lit 15093312645) (nat_lit 0) A10K2.u6962 from rfl, allE_node, arows6961, irow6963, arows6962]
  all_goals rfl

theorem atot6963 : totK PA10K2 A10K2.u6963 = [0, 244406495887, 2555283356593, 7034995235964, 7283459772396, 2642930806173, 271497475243, 6632180018, 0, 0] := by
  rw [show A10K2.u6963 = KTree.node A10K2.u6961 (nat_lit 116096478) (nat_lit 15093312645) (nat_lit 0) A10K2.u6962 from rfl, totK_node, atot6961, atot6962]
  decide +kernel

theorem arows6966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6966 = true := by
  rw [show A10K2.u6966 = KTree.node A10K2.u6964 (nat_lit 116109278) (nat_lit 14808078831) (nat_lit 0) A10K2.u6965 from rfl, allE_node, arows6964, irow6966, arows6965]
  all_goals rfl

theorem atot6966 : totK PA10K2 A10K2.u6966 = [0, 0, 1336763410276, 5856581487448, 8187361936720, 3934029659512, 469007077700, 7047025452, 0, 0] := by
  rw [show A10K2.u6966 = KTree.node A10K2.u6964 (nat_lit 116109278) (nat_lit 14808078831) (nat_lit 0) A10K2.u6965 from rfl, totK_node, atot6964, atot6965]
  decide +kernel

theorem arows6973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6973 = true := by
  rw [show A10K2.u6973 = KTree.node A10K2.u6971 (nat_lit 116129015) (nat_lit 14693586544) (nat_lit 0) A10K2.u6972 from rfl, allE_node, arows6971, irow6973, arows6972]
  all_goals rfl

theorem atot6973 : totK PA10K2 A10K2.u6973 = [0, 0, 1174723242065, 5108417534551, 7670781094590, 4633334096362, 999922661591, 61110126106, 0, 0] := by
  rw [show A10K2.u6973 = KTree.node A10K2.u6971 (nat_lit 116129015) (nat_lit 14693586544) (nat_lit 0) A10K2.u6972 from rfl, totK_node, atot6971, atot6972]
  decide +kernel

theorem arows6976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6976 = true := by
  rw [show A10K2.u6976 = KTree.node A10K2.u6974 (nat_lit 116213238) (nat_lit 16055129594) (nat_lit 0) A10K2.u6975 from rfl, allE_node, arows6974, irow6976, arows6975]
  all_goals rfl

theorem atot6976 : totK PA10K2 A10K2.u6976 = [0, 0, 889131725979, 4589237673134, 7944630275043, 4810322039757, 841523654483, 37525842271, 0, 0] := by
  rw [show A10K2.u6976 = KTree.node A10K2.u6974 (nat_lit 116213238) (nat_lit 16055129594) (nat_lit 0) A10K2.u6975 from rfl, totK_node, atot6974, atot6975]
  decide +kernel

theorem arows6980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6980 = true := by
  rw [show A10K2.u6980 = KTree.node A10K2.u6978 (nat_lit 116225968) (nat_lit 12433497429) (nat_lit 0) A10K2.u6979 from rfl, allE_node, arows6978, irow6980, arows6979]
  all_goals rfl

theorem atot6980 : totK PA10K2 A10K2.u6980 = [0, 0, 496604236678, 3640514737458, 7950048576224, 6155903674154, 1418635036993, 73133025948, 0, 0] := by
  rw [show A10K2.u6980 = KTree.node A10K2.u6978 (nat_lit 116225968) (nat_lit 12433497429) (nat_lit 0) A10K2.u6979 from rfl, totK_node, atot6978, atot6979]
  decide +kernel

theorem arows6983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6983 = true := by
  rw [show A10K2.u6983 = KTree.node A10K2.u6981 (nat_lit 116246675) (nat_lit 10817113888) (nat_lit 0) A10K2.u6982 from rfl, allE_node, arows6981, irow6983, arows6982]
  all_goals rfl

theorem atot6983 : totK PA10K2 A10K2.u6983 = [0, 0, 304922396905, 2053098711157, 6219863965959, 7516284040224, 2989879099471, 360160656740, 7380853412, 0] := by
  rw [show A10K2.u6983 = KTree.node A10K2.u6981 (nat_lit 116246675) (nat_lit 10817113888) (nat_lit 0) A10K2.u6982 from rfl, totK_node, atot6981, atot6982]
  decide +kernel

theorem arows6988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6988 = true := by
  rw [show A10K2.u6988 = KTree.node A10K2.u6986 (nat_lit 116279524) (nat_lit 13617425715) (nat_lit 0) A10K2.u6987 from rfl, allE_node, arows6986, irow6988, arows6987]
  all_goals rfl

theorem atot6988 : totK PA10K2 A10K2.u6988 = [0, 0, 1607261656225, 6606085870605, 8094075248259, 2912640330493, 300474720002, 6354482628, 0, 0] := by
  rw [show A10K2.u6988 = KTree.node A10K2.u6986 (nat_lit 116279524) (nat_lit 13617425715) (nat_lit 0) A10K2.u6987 from rfl, totK_node, atot6986, atot6987]
  decide +kernel

theorem arows6991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6991 = true := by
  rw [show A10K2.u6991 = KTree.node A10K2.u6989 (nat_lit 116337434) (nat_lit 12802278115) (nat_lit 0) A10K2.u6990 from rfl, allE_node, arows6989, irow6991, arows6990]
  all_goals rfl

theorem atot6991 : totK PA10K2 A10K2.u6991 = [0, 0, 855226884452, 4617291987063, 8292048410881, 5167394360537, 791604860838, 19417837436, 0, 0] := by
  rw [show A10K2.u6991 = KTree.node A10K2.u6989 (nat_lit 116337434) (nat_lit 12802278115) (nat_lit 0) A10K2.u6990 from rfl, totK_node, atot6989, atot6990]
  decide +kernel

theorem arows6995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6995 = true := by
  rw [show A10K2.u6995 = KTree.node A10K2.u6993 (nat_lit 116355576) (nat_lit 13299278290) (nat_lit 0) A10K2.u6994 from rfl, allE_node, arows6993, irow6995, arows6994]
  all_goals rfl

theorem atot6995 : totK PA10K2 A10K2.u6995 = [0, 310694887869, 1854030442570, 5048956968612, 7002610911825, 4537881707640, 1030724339763, 62382159641, 0, 0] := by
  rw [show A10K2.u6995 = KTree.node A10K2.u6993 (nat_lit 116355576) (nat_lit 13299278290) (nat_lit 0) A10K2.u6994 from rfl, totK_node, atot6993, atot6994]
  decide +kernel

theorem arows6998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6998 = true := by
  rw [show A10K2.u6998 = KTree.node A10K2.u6996 (nat_lit 116922942) (nat_lit 10910595538) (nat_lit 0) A10K2.u6997 from rfl, allE_node, arows6996, irow6998, arows6997]
  all_goals rfl

theorem atot6998 : totK PA10K2 A10K2.u6998 = [0, 1116656698819, 5196234616369, 7857794247346, 4148114147415, 678472353889, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6998 = KTree.node A10K2.u6996 (nat_lit 116922942) (nat_lit 10910595538) (nat_lit 0) A10K2.u6997 from rfl, totK_node, atot6996, atot6997]
  decide +kernel

theorem arows7004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7004 = true := by
  rw [show A10K2.u7004 = KTree.node A10K2.u7002 (nat_lit 116945815) (nat_lit 14233336443) (nat_lit 0) A10K2.u7003 from rfl, allE_node, arows7002, irow7004, arows7003]
  all_goals rfl

theorem atot7004 : totK PA10K2 A10K2.u7004 = [0, 653619017713, 3926776076456, 7934344631869, 6024991417652, 1478291821777, 88646843074, 0, 0, 0] := by
  rw [show A10K2.u7004 = KTree.node A10K2.u7002 (nat_lit 116945815) (nat_lit 14233336443) (nat_lit 0) A10K2.u7003 from rfl, totK_node, atot7002, atot7003]
  decide +kernel

theorem arows7007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7007 = true := by
  rw [show A10K2.u7007 = KTree.node A10K2.u7005 (nat_lit 116965420) (nat_lit 12812578913) (nat_lit 0) A10K2.u7006 from rfl, allE_node, arows7005, irow7007, arows7006]
  all_goals rfl

theorem atot7007 : totK PA10K2 A10K2.u7007 = [0, 0, 1132170314236, 5398406186495, 8053883900820, 3886803592152, 525783637798, 12477124820, 0, 0] := by
  rw [show A10K2.u7007 = KTree.node A10K2.u7005 (nat_lit 116965420) (nat_lit 12812578913) (nat_lit 0) A10K2.u7006 from rfl, totK_node, atot7005, atot7006]
  decide +kernel

theorem arows7011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7011 = true := by
  rw [show A10K2.u7011 = KTree.node A10K2.u7009 (nat_lit 116992838) (nat_lit 11933677) (nat_lit 0) A10K2.u7010 from rfl, allE_node, arows7009, irow7011, arows7010]
  all_goals rfl

theorem atot7011 : totK PA10K2 A10K2.u7011 = [0, 811040046021, 4218913077588, 7618647845331, 5527934942593, 1379680406728, 89094959633, 0, 0, 0] := by
  rw [show A10K2.u7011 = KTree.node A10K2.u7009 (nat_lit 116992838) (nat_lit 11933677) (nat_lit 0) A10K2.u7010 from rfl, totK_node, atot7009, atot7010]
  decide +kernel

theorem arows7014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7014 = true := by
  rw [show A10K2.u7014 = KTree.node A10K2.u7012 (nat_lit 117007702) (nat_lit 11886913796) (nat_lit 0) A10K2.u7013 from rfl, allE_node, arows7012, irow7014, arows7013]
  all_goals rfl

theorem atot7014 : totK PA10K2 A10K2.u7014 = [0, 1277311426415, 5639847810663, 8180634158399, 4210172598184, 638200566058, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u7014 = KTree.node A10K2.u7012 (nat_lit 117007702) (nat_lit 11886913796) (nat_lit 0) A10K2.u7013 from rfl, totK_node, atot7012, atot7013]
  decide +kernel

theorem arows7019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7019 = true := by
  rw [show A10K2.u7019 = KTree.node A10K2.u7017 (nat_lit 117026227) (nat_lit 9643228669) (nat_lit 0) A10K2.u7018 from rfl, allE_node, arows7017, irow7019, arows7018]
  all_goals rfl

theorem atot7019 : totK PA10K2 A10K2.u7019 = [0, 0, 1403258665812, 5815593582975, 7868310927923, 3749304481085, 530938681778, 12696458652, 0, 0] := by
  rw [show A10K2.u7019 = KTree.node A10K2.u7017 (nat_lit 117026227) (nat_lit 9643228669) (nat_lit 0) A10K2.u7018 from rfl, totK_node, atot7017, atot7018]
  decide +kernel

theorem arows7022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7022 = true := by
  rw [show A10K2.u7022 = KTree.node A10K2.u7020 (nat_lit 117042225) (nat_lit 9400277524) (nat_lit 0) A10K2.u7021 from rfl, allE_node, arows7020, irow7022, arows7021]
  all_goals rfl

theorem atot7022 : totK PA10K2 A10K2.u7022 = [0, 762038499923, 3594455001394, 6817892298212, 6230147688177, 2131399367194, 138450876937, 0, 0, 0] := by
  rw [show A10K2.u7022 = KTree.node A10K2.u7020 (nat_lit 117042225) (nat_lit 9400277524) (nat_lit 0) A10K2.u7021 from rfl, totK_node, atot7020, atot7021]
  decide +kernel

theorem arows7026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7026 = true := by
  rw [show A10K2.u7026 = KTree.node A10K2.u7024 (nat_lit 117122951) (nat_lit 14096367277) (nat_lit 0) A10K2.u7025 from rfl, allE_node, arows7024, irow7026, arows7025]
  all_goals rfl

theorem atot7026 : totK PA10K2 A10K2.u7026 = [0, 765763168051, 4351925312326, 8033303227892, 5284035107373, 1023601151348, 35255389389, 0, 0, 0] := by
  rw [show A10K2.u7026 = KTree.node A10K2.u7024 (nat_lit 117122951) (nat_lit 14096367277) (nat_lit 0) A10K2.u7025 from rfl, totK_node, atot7024, atot7025]
  decide +kernel

theorem arows7029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7029 = true := by
  rw [show A10K2.u7029 = KTree.node A10K2.u7027 (nat_lit 117141431) (nat_lit 15196976937) (nat_lit 0) A10K2.u7028 from rfl, allE_node, arows7027, irow7029, arows7028]
  all_goals rfl

theorem atot7029 : totK PA10K2 A10K2.u7029 = [0, 896434737838, 4557872759243, 7941775244445, 5359680830277, 1179989472103, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u7029 = KTree.node A10K2.u7027 (nat_lit 117141431) (nat_lit 15196976937) (nat_lit 0) A10K2.u7028 from rfl, totK_node, atot7027, atot7028]
  decide +kernel

theorem arows7037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7037 = true := by
  rw [show A10K2.u7037 = KTree.node A10K2.u7035 (nat_lit 117151845) (nat_lit 6214282894) (nat_lit 0) A10K2.u7036 from rfl, allE_node, arows7035, irow7037, arows7036]
  all_goals rfl

theorem atot7037 : totK PA10K2 A10K2.u7037 = [0, 0, 1339144630668, 5949688158636, 8256142585121, 3646182802921, 387849956277, 6904928264, 0, 0] := by
  rw [show A10K2.u7037 = KTree.node A10K2.u7035 (nat_lit 117151845) (nat_lit 6214282894) (nat_lit 0) A10K2.u7036 from rfl, totK_node, atot7035, atot7036]
  decide +kernel

theorem arows7040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7040 = true := by
  rw [show A10K2.u7040 = KTree.node A10K2.u7038 (nat_lit 117172069) (nat_lit 2924912364) (nat_lit 0) A10K2.u7039 from rfl, allE_node, arows7038, irow7040, arows7039]
  all_goals rfl

theorem atot7040 : totK PA10K2 A10K2.u7040 = [0, 0, 895145480297, 4777470592312, 8283218140339, 5003602768764, 745970815478, 19271132487, 0, 0] := by
  rw [show A10K2.u7040 = KTree.node A10K2.u7038 (nat_lit 117172069) (nat_lit 2924912364) (nat_lit 0) A10K2.u7039 from rfl, totK_node, atot7038, atot7039]
  decide +kernel

theorem arows7044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7044 = true := by
  rw [show A10K2.u7044 = KTree.node A10K2.u7042 (nat_lit 117182358) (nat_lit 15675777247) (nat_lit 0) A10K2.u7043 from rfl, allE_node, arows7042, irow7044, arows7043]
  all_goals rfl

theorem atot7044 : totK PA10K2 A10K2.u7044 = [0, 0, 1173709806563, 4993925418436, 7453144810261, 4596828045433, 1028962901471, 61363143891, 0, 0] := by
  rw [show A10K2.u7044 = KTree.node A10K2.u7042 (nat_lit 117182358) (nat_lit 15675777247) (nat_lit 0) A10K2.u7043 from rfl, totK_node, atot7042, atot7043]
  decide +kernel

theorem arows7047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7047 = true := by
  rw [show A10K2.u7047 = KTree.node A10K2.u7045 (nat_lit 117206596) (nat_lit 9543987874) (nat_lit 0) A10K2.u7046 from rfl, allE_node, arows7045, irow7047, arows7046]
  all_goals rfl

theorem atot7047 : totK PA10K2 A10K2.u7047 = [0, 0, 900318328081, 4660817031242, 8051849469218, 5230507027742, 1099794890490, 62351816811, 0, 0] := by
  rw [show A10K2.u7047 = KTree.node A10K2.u7045 (nat_lit 117206596) (nat_lit 9543987874) (nat_lit 0) A10K2.u7046 from rfl, totK_node, atot7045, atot7046]
  decide +kernel

theorem arows7052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7052 = true := by
  rw [show A10K2.u7052 = KTree.node A10K2.u7050 (nat_lit 117217351) (nat_lit 6733464721) (nat_lit 0) A10K2.u7051 from rfl, allE_node, arows7050, irow7052, arows7051]
  all_goals rfl

theorem atot7052 : totK PA10K2 A10K2.u7052 = [0, 0, 0, 1720406734723, 6821531954002, 7867310462216, 2684699462295, 261543932641, 6725424603, 0] := by
  rw [show A10K2.u7052 = KTree.node A10K2.u7050 (nat_lit 117217351) (nat_lit 6733464721) (nat_lit 0) A10K2.u7051 from rfl, totK_node, atot7050, atot7051]
  decide +kernel

theorem arows7055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7055 = true := by
  rw [show A10K2.u7055 = KTree.node A10K2.u7053 (nat_lit 117255799) (nat_lit 14402880528) (nat_lit 0) A10K2.u7054 from rfl, allE_node, arows7053, irow7055, arows7054]
  all_goals rfl

theorem atot7055 : totK PA10K2 A10K2.u7055 = [0, 0, 1081840141366, 4879143473544, 7619772881240, 4854414449244, 1074556011573, 63122149300, 0, 0] := by
  rw [show A10K2.u7055 = KTree.node A10K2.u7053 (nat_lit 117255799) (nat_lit 14402880528) (nat_lit 0) A10K2.u7054 from rfl, totK_node, atot7053, atot7054]
  decide +kernel

theorem arows7059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7059 = true := by
  rw [show A10K2.u7059 = KTree.node A10K2.u7057 (nat_lit 117272023) (nat_lit 14430147840) (nat_lit 0) A10K2.u7058 from rfl, allE_node, arows7057, irow7059, arows7058]
  all_goals rfl

theorem atot7059 : totK PA10K2 A10K2.u7059 = [0, 0, 999573930879, 4903787708030, 7986599795922, 5066134315234, 1075987209824, 62364134685, 0, 0] := by
  rw [show A10K2.u7059 = KTree.node A10K2.u7057 (nat_lit 117272023) (nat_lit 14430147840) (nat_lit 0) A10K2.u7058 from rfl, totK_node, atot7057, atot7058]
  decide +kernel

theorem arows7062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7062 = true := by
  rw [show A10K2.u7062 = KTree.node A10K2.u7060 (nat_lit 117290902) (nat_lit 14962738667) (nat_lit 0) A10K2.u7061 from rfl, allE_node, arows7060, irow7062, arows7061]
  all_goals rfl

theorem atot7062 : totK PA10K2 A10K2.u7062 = [0, 0, 0, 1867413625526, 6889643634242, 7814552326726, 2759549034558, 272885886227, 6860445330, 0] := by
  rw [show A10K2.u7062 = KTree.node A10K2.u7060 (nat_lit 117290902) (nat_lit 14962738667) (nat_lit 0) A10K2.u7061 from rfl, totK_node, atot7060, atot7061]
  decide +kernel

theorem arows7068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7068 = true := by
  rw [show A10K2.u7068 = KTree.node A10K2.u7066 (nat_lit 117379030) (nat_lit 15605321001) (nat_lit 0) A10K2.u7067 from rfl, allE_node, arows7066, irow7068, arows7067]
  all_goals rfl

theorem atot7068 : totK PA10K2 A10K2.u7068 = [0, 0, 1208361294890, 5153907303542, 7548743951955, 4481129486873, 967965154696, 62126577537, 0, 0] := by
  rw [show A10K2.u7068 = KTree.node A10K2.u7066 (nat_lit 117379030) (nat_lit 15605321001) (nat_lit 0) A10K2.u7067 from rfl, totK_node, atot7066, atot7067]
  decide +kernel

theorem arows7071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7071 = true := by
  rw [show A10K2.u7071 = KTree.node A10K2.u7069 (nat_lit 117399815) (nat_lit 10714725979) (nat_lit 0) A10K2.u7070 from rfl, allE_node, arows7069, irow7071, arows7070]
  all_goals rfl

theorem atot7071 : totK PA10K2 A10K2.u7071 = [0, 0, 1199428634829, 5522183678840, 8290940794515, 4297156462004, 522651396364, 11918539728, 0, 0] := by
  rw [show A10K2.u7071 = KTree.node A10K2.u7069 (nat_lit 117399815) (nat_lit 10714725979) (nat_lit 0) A10K2.u7070 from rfl, totK_node, atot7069, atot7070]
  decide +kernel

theorem arows7075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7075 = true := by
  rw [show A10K2.u7075 = KTree.node A10K2.u7073 (nat_lit 117409793) (nat_lit 10503824933) (nat_lit 0) A10K2.u7074 from rfl, allE_node, arows7073, irow7075, arows7074]
  all_goals rfl

theorem atot7075 : totK PA10K2 A10K2.u7075 = [0, 0, 0, 1542335816073, 6279506643996, 8128244105353, 3210577486622, 345358926942, 6318667960, 0] := by
  rw [show A10K2.u7075 = KTree.node A10K2.u7073 (nat_lit 117409793) (nat_lit 10503824933) (nat_lit 0) A10K2.u7074 from rfl, totK_node, atot7073, atot7074]
  decide +kernel

theorem arows7078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7078 = true := by
  rw [show A10K2.u7078 = KTree.node A10K2.u7076 (nat_lit 117423317) (nat_lit 4594118279) (nat_lit 0) A10K2.u7077 from rfl, allE_node, arows7076, irow7078, arows7077]
  all_goals rfl

theorem atot7078 : totK PA10K2 A10K2.u7078 = [0, 0, 0, 1450344805603, 6220534865051, 8212318694720, 3405503183515, 360673199290, 6439430839, 0] := by
  rw [show A10K2.u7078 = KTree.node A10K2.u7076 (nat_lit 117423317) (nat_lit 4594118279) (nat_lit 0) A10K2.u7077 from rfl, totK_node, atot7076, atot7077]
  decide +kernel

theorem arows7083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7083 = true := by
  rw [show A10K2.u7083 = KTree.node A10K2.u7081 (nat_lit 117441028) (nat_lit 11890603812) (nat_lit 0) A10K2.u7082 from rfl, allE_node, arows7081, irow7083, arows7082]
  all_goals rfl

theorem atot7083 : totK PA10K2 A10K2.u7083 = [0, 869900121985, 3497345818905, 4549598790853, 2947992873571, 3392447472248, 3175526443122, 910141810368, 61018386929, 0] := by
  rw [show A10K2.u7083 = KTree.node A10K2.u7081 (nat_lit 117441028) (nat_lit 11890603812) (nat_lit 0) A10K2.u7082 from rfl, totK_node, atot7081, atot7082]
  decide +kernel

theorem arows7086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7086 = true := by
  rw [show A10K2.u7086 = KTree.node A10K2.u7084 (nat_lit 117459242) (nat_lit 11960336315) (nat_lit 0) A10K2.u7085 from rfl, allE_node, arows7084, irow7086, arows7085]
  all_goals rfl

theorem atot7086 : totK PA10K2 A10K2.u7086 = [0, 1159255197828, 5208264658044, 7807228070093, 4037276234920, 544545889352, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u7086 = KTree.node A10K2.u7084 (nat_lit 117459242) (nat_lit 11960336315) (nat_lit 0) A10K2.u7085 from rfl, totK_node, atot7084, atot7085]
  decide +kernel

theorem arows7090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7090 = true := by
  rw [show A10K2.u7090 = KTree.node A10K2.u7088 (nat_lit 117472699) (nat_lit 6840547996) (nat_lit 0) A10K2.u7089 from rfl, allE_node, arows7088, irow7090, arows7089]
  all_goals rfl

theorem atot7090 : totK PA10K2 A10K2.u7090 = [0, 309893393367, 3043474368527, 7806041451071, 6887159630718, 1773796685002, 100684614486, 0, 0, 0] := by
  rw [show A10K2.u7090 = KTree.node A10K2.u7088 (nat_lit 117472699) (nat_lit 6840547996) (nat_lit 0) A10K2.u7089 from rfl, totK_node, atot7088, atot7089]
  decide +kernel

theorem arows7093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7093 = true := by
  rw [show A10K2.u7093 = KTree.node A10K2.u7091 (nat_lit 117490517) (nat_lit 6300289349) (nat_lit 0) A10K2.u7092 from rfl, allE_node, arows7091, irow7093, arows7092]
  all_goals rfl

theorem atot7093 : totK PA10K2 A10K2.u7093 = [0, 0, 865385310994, 4577427530411, 7743845890397, 4325237379546, 773699802715, 36196801203, 0, 0] := by
  rw [show A10K2.u7093 = KTree.node A10K2.u7091 (nat_lit 117490517) (nat_lit 6300289349) (nat_lit 0) A10K2.u7092 from rfl, totK_node, atot7091, atot7092]
  decide +kernel

theorem arows7100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7100 = true := by
  rw [show A10K2.u7100 = KTree.node A10K2.u7098 (nat_lit 117573668) (nat_lit 13584738429) (nat_lit 0) A10K2.u7099 from rfl, allE_node, arows7098, irow7100, arows7099]
  all_goals rfl

theorem atot7100 : totK PA10K2 A10K2.u7100 = [0, 795409072615, 4077100836737, 7584303840155, 5713444716298, 1484698179476, 102682681223, 0, 0, 0] := by
  rw [show A10K2.u7100 = KTree.node A10K2.u7098 (nat_lit 117573668) (nat_lit 13584738429) (nat_lit 0) A10K2.u7099 from rfl, totK_node, atot7098, atot7099]
  decide +kernel

theorem arows7103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7103 = true := by
  rw [show A10K2.u7103 = KTree.node A10K2.u7101 (nat_lit 117589333) (nat_lit 6910226604) (nat_lit 0) A10K2.u7102 from rfl, allE_node, arows7101, irow7103, arows7102]
  all_goals rfl

theorem atot7103 : totK PA10K2 A10K2.u7103 = [0, 994376428588, 4985782705419, 7889770087830, 4264009723452, 656123304284, 17849191082, 0, 0, 0] := by
  rw [show A10K2.u7103 = KTree.node A10K2.u7101 (nat_lit 117589333) (nat_lit 6910226604) (nat_lit 0) A10K2.u7102 from rfl, totK_node, atot7101, atot7102]
  decide +kernel

theorem arows7107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7107 = true := by
  rw [show A10K2.u7107 = KTree.node A10K2.u7105 (nat_lit 117621001) (nat_lit 9757796508) (nat_lit 0) A10K2.u7106 from rfl, allE_node, arows7105, irow7107, arows7106]
  all_goals rfl

theorem atot7107 : totK PA10K2 A10K2.u7107 = [0, 0, 1607350395494, 6791522229313, 8065441212733, 2339383771938, 139685856413, 0, 0, 0] := by
  rw [show A10K2.u7107 = KTree.node A10K2.u7105 (nat_lit 117621001) (nat_lit 9757796508) (nat_lit 0) A10K2.u7106 from rfl, totK_node, atot7105, atot7106]
  decide +kernel

theorem arows7110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7110 = true := by
  rw [show A10K2.u7110 = KTree.node A10K2.u7108 (nat_lit 117641325) (nat_lit 5350984849) (nat_lit 0) A10K2.u7109 from rfl, allE_node, arows7108, irow7110, arows7109]
  all_goals rfl

theorem atot7110 : totK PA10K2 A10K2.u7110 = [0, 1322837559556, 5466500761055, 7530035306702, 4182452458031, 1160238058011, 162361018811, 6354482628, 0, 0] := by
  rw [show A10K2.u7110 = KTree.node A10K2.u7108 (nat_lit 117641325) (nat_lit 5350984849) (nat_lit 0) A10K2.u7109 from rfl, totK_node, atot7108, atot7109]
  decide +kernel

theorem arows7115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7115 = true := by
  rw [show A10K2.u7115 = KTree.node A10K2.u7113 (nat_lit 117664825) (nat_lit 7244271112) (nat_lit 0) A10K2.u7114 from rfl, allE_node, arows7113, irow7115, arows7114]
  all_goals rfl

theorem atot7115 : totK PA10K2 A10K2.u7115 = [0, 845700278790, 4654188602551, 8464829752918, 5428511305438, 945198186101, 27313355902, 0, 0, 0] := by
  rw [show A10K2.u7115 = KTree.node A10K2.u7113 (nat_lit 117664825) (nat_lit 7244271112) (nat_lit 0) A10K2.u7114 from rfl, totK_node, atot7113, atot7114]
  decide +kernel

theorem arows7118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7118 = true := by
  rw [show A10K2.u7118 = KTree.node A10K2.u7116 (nat_lit 117674028) (nat_lit 11179126718) (nat_lit 0) A10K2.u7117 from rfl, allE_node, arows7116, irow7118, arows7117]
  all_goals rfl

theorem atot7118 : totK PA10K2 A10K2.u7118 = [0, 0, 1321655350146, 5904656022463, 8421322822676, 3856776443332, 442556447188, 6904928264, 0, 0] := by
  rw [show A10K2.u7118 = KTree.node A10K2.u7116 (nat_lit 117674028) (nat_lit 11179126718) (nat_lit 0) A10K2.u7117 from rfl, totK_node, atot7116, atot7117]
  decide +kernel

theorem arows7122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7122 = true := by
  rw [show A10K2.u7122 = KTree.node A10K2.u7120 (nat_lit 117697920) (nat_lit 14919532568) (nat_lit 0) A10K2.u7121 from rfl, allE_node, arows7120, irow7122, arows7121]
  all_goals rfl

theorem atot7122 : totK PA10K2 A10K2.u7122 = [0, 0, 844899945287, 4448938223640, 8114450591110, 5605838005161, 1044781893799, 30846741173, 0, 0] := by
  rw [show A10K2.u7122 = KTree.node A10K2.u7120 (nat_lit 117697920) (nat_lit 14919532568) (nat_lit 0) A10K2.u7121 from rfl, totK_node, atot7120, atot7121]
  decide +kernel

theorem arows7125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7125 = true := by
  rw [show A10K2.u7125 = KTree.node A10K2.u7123 (nat_lit 117706871) (nat_lit 13860624898) (nat_lit 0) A10K2.u7124 from rfl, allE_node, arows7123, irow7125, arows7124]
  all_goals rfl

theorem atot7125 : totK PA10K2 A10K2.u7125 = [0, 0, 1278187266994, 5371429553888, 7592294444815, 4068703488262, 860905994632, 68142084271, 0, 0] := by
  rw [show A10K2.u7125 = KTree.node A10K2.u7123 (nat_lit 117706871) (nat_lit 13860624898) (nat_lit 0) A10K2.u7124 from rfl, totK_node, atot7123, atot7124]
  decide +kernel

theorem arows7131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7131 = true := by
  rw [show A10K2.u7131 = KTree.node A10K2.u7129 (nat_lit 117727758) (nat_lit 13708908750) (nat_lit 0) A10K2.u7130 from rfl, allE_node, arows7129, irow7131, arows7130]
  all_goals rfl

theorem atot7131 : totK PA10K2 A10K2.u7131 = [0, 0, 1056700981572, 5218792095407, 8169809740150, 4169393567421, 574710787001, 12558367923, 0, 0] := by
  rw [show A10K2.u7131 = KTree.node A10K2.u7129 (nat_lit 117727758) (nat_lit 13708908750) (nat_lit 0) A10K2.u7130 from rfl, totK_node, atot7129, atot7130]
  decide +kernel

theorem arows7134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7134 = true := by
  rw [show A10K2.u7134 = KTree.node A10K2.u7132 (nat_lit 117739001) (nat_lit 6324186901) (nat_lit 0) A10K2.u7133 from rfl, allE_node, arows7132, irow7134, arows7133]
  all_goals rfl

theorem atot7134 : totK PA10K2 A10K2.u7134 = [0, 0, 0, 1412165865137, 5830123416042, 7572057062093, 3510401313296, 603836708998, 30605747850, 0] := by
  rw [show A10K2.u7134 = KTree.node A10K2.u7132 (nat_lit 117739001) (nat_lit 6324186901) (nat_lit 0) A10K2.u7133 from rfl, totK_node, atot7132, atot7133]
  decide +kernel

theorem arows7138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7138 = true := by
  rw [show A10K2.u7138 = KTree.node A10K2.u7136 (nat_lit 117760072) (nat_lit 13784267902) (nat_lit 0) A10K2.u7137 from rfl, allE_node, arows7136, irow7138, arows7137]
  all_goals rfl

theorem atot7138 : totK PA10K2 A10K2.u7138 = [0, 0, 470372318891, 2687602573781, 6268026510909, 6628006582812, 2425360832319, 271643173512, 5528811039, 0] := by
  rw [show A10K2.u7138 = KTree.node A10K2.u7136 (nat_lit 117760072) (nat_lit 13784267902) (nat_lit 0) A10K2.u7137 from rfl, totK_node, atot7136, atot7137]
  decide +kernel

theorem arows7141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7141 = true := by
  rw [show A10K2.u7141 = KTree.node A10K2.u7139 (nat_lit 117841010) (nat_lit 9942553201) (nat_lit 0) A10K2.u7140 from rfl, allE_node, arows7139, irow7141, arows7140]
  all_goals rfl

theorem atot7141 : totK PA10K2 A10K2.u7141 = [0, 0, 1103834736391, 5038353599404, 7854482929601, 4299225374385, 724186299396, 36865889447, 0, 0] := by
  rw [show A10K2.u7141 = KTree.node A10K2.u7139 (nat_lit 117841010) (nat_lit 9942553201) (nat_lit 0) A10K2.u7140 from rfl, totK_node, atot7139, atot7140]
  decide +kernel

theorem arows7146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7146 = true := by
  rw [show A10K2.u7146 = KTree.node A10K2.u7144 (nat_lit 117867126) (nat_lit 14024337225) (nat_lit 0) A10K2.u7145 from rfl, allE_node, arows7144, irow7146, arows7145]
  all_goals rfl

theorem atot7146 : totK PA10K2 A10K2.u7146 = [0, 0, 214452326151, 3016619022244, 7897523082595, 6210756836132, 1275145365047, 70459460067, 0, 0] := by
  rw [show A10K2.u7146 = KTree.node A10K2.u7144 (nat_lit 117867126) (nat_lit 14024337225) (nat_lit 0) A10K2.u7145 from rfl, totK_node, atot7144, atot7145]
  decide +kernel

theorem arows7149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7149 = true := by
  rw [show A10K2.u7149 = KTree.node A10K2.u7147 (nat_lit 117899378) (nat_lit 9658301811) (nat_lit 0) A10K2.u7148 from rfl, allE_node, arows7147, irow7149, arows7148]
  all_goals rfl

theorem atot7149 : totK PA10K2 A10K2.u7149 = [0, 0, 807311024672, 3718100158688, 6649022436359, 5617838350522, 1881877986148, 223671996152, 5676195732, 0] := by
  rw [show A10K2.u7149 = KTree.node A10K2.u7147 (nat_lit 117899378) (nat_lit 9658301811) (nat_lit 0) A10K2.u7148 from rfl, totK_node, atot7147, atot7148]
  decide +kernel

theorem arows7153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7153 = true := by
  rw [show A10K2.u7153 = KTree.node A10K2.u7151 (nat_lit 117913299) (nat_lit 10672529566) (nat_lit 0) A10K2.u7152 from rfl, allE_node, arows7151, irow7153, arows7152]
  all_goals rfl

theorem atot7153 : totK PA10K2 A10K2.u7153 = [0, 0, 1356831199287, 5921019284834, 8402740958549, 4120392054631, 547065340411, 12406286802, 0, 0] := by
  rw [show A10K2.u7153 = KTree.node A10K2.u7151 (nat_lit 117913299) (nat_lit 10672529566) (nat_lit 0) A10K2.u7152 from rfl, totK_node, atot7151, atot7152]
  decide +kernel

theorem arows7156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7156 = true := by
  rw [show A10K2.u7156 = KTree.node A10K2.u7154 (nat_lit 118489476) (nat_lit 9077674953) (nat_lit 0) A10K2.u7155 from rfl, allE_node, arows7154, irow7156, arows7155]
  all_goals rfl

theorem atot7156 : totK PA10K2 A10K2.u7156 = [0, 839403861465, 3377909017557, 5271112084909, 5292111019264, 3822266820564, 1028111244420, 62368562949, 0, 0] := by
  rw [show A10K2.u7156 = KTree.node A10K2.u7154 (nat_lit 118489476) (nat_lit 9077674953) (nat_lit 0) A10K2.u7155 from rfl, totK_node, atot7154, atot7155]
  decide +kernel

theorem arows7167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7167 = true := by
  rw [show A10K2.u7167 = KTree.node A10K2.u7165 (nat_lit 118507688) (nat_lit 8917934252) (nat_lit 0) A10K2.u7166 from rfl, allE_node, arows7165, irow7167, arows7166]
  all_goals rfl

theorem atot7167 : totK PA10K2 A10K2.u7167 = [0, 1047320617618, 5017123156767, 7914216886317, 4349676230171, 669606999199, 17115393699, 0, 0, 0] := by
  rw [show A10K2.u7167 = KTree.node A10K2.u7165 (nat_lit 118507688) (nat_lit 8917934252) (nat_lit 0) A10K2.u7166 from rfl, totK_node, atot7165, atot7166]
  decide +kernel

theorem arows7170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7170 = true := by
  rw [show A10K2.u7170 = KTree.node A10K2.u7168 (nat_lit 118522149) (nat_lit 7314703828) (nat_lit 0) A10K2.u7169 from rfl, allE_node, arows7168, irow7170, arows7169]
  all_goals rfl

theorem atot7170 : totK PA10K2 A10K2.u7170 = [0, 295757175837, 2562065442966, 6939666914423, 7160522017543, 2502064960432, 332607032806, 20060612110, 0, 0] := by
  rw [show A10K2.u7170 = KTree.node A10K2.u7168 (nat_lit 118522149) (nat_lit 7314703828) (nat_lit 0) A10K2.u7169 from rfl, totK_node, atot7168, atot7169]
  decide +kernel

theorem arows7174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7174 = true := by
  rw [show A10K2.u7174 = KTree.node A10K2.u7172 (nat_lit 118540564) (nat_lit 13357073411) (nat_lit 0) A10K2.u7173 from rfl, allE_node, arows7172, irow7174, arows7173]
  all_goals rfl

theorem atot7174 : totK PA10K2 A10K2.u7174 = [0, 0, 1244165171961, 5533277407317, 7912373543013, 3724352415334, 541838969248, 16136189093, 0, 0] := by
  rw [show A10K2.u7174 = KTree.node A10K2.u7172 (nat_lit 118540564) (nat_lit 13357073411) (nat_lit 0) A10K2.u7173 from rfl, totK_node, atot7172, atot7173]
  decide +kernel

theorem arows7177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7177 = true := by
  rw [show A10K2.u7177 = KTree.node A10K2.u7175 (nat_lit 118624306) (nat_lit 6569989804) (nat_lit 0) A10K2.u7176 from rfl, allE_node, arows7175, irow7177, arows7176]
  all_goals rfl

theorem atot7177 : totK PA10K2 A10K2.u7177 = [0, 1219014644614, 5087031653211, 7519373293434, 4532718225265, 1036016681058, 61661003203, 0, 0, 0] := by
  rw [show A10K2.u7177 = KTree.node A10K2.u7175 (nat_lit 118624306) (nat_lit 6569989804) (nat_lit 0) A10K2.u7176 from rfl, totK_node, atot7175, atot7176]
  decide +kernel

theorem arows7182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7182 = true := by
  rw [show A10K2.u7182 = KTree.node A10K2.u7180 (nat_lit 118637726) (nat_lit 13295944046) (nat_lit 0) A10K2.u7181 from rfl, allE_node, arows7180, irow7182, arows7181]
  all_goals rfl

theorem atot7182 : totK PA10K2 A10K2.u7182 = [0, 928536070374, 4946475012182, 8092214401810, 4293260254146, 645156898411, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7182 = KTree.node A10K2.u7180 (nat_lit 118637726) (nat_lit 13295944046) (nat_lit 0) A10K2.u7181 from rfl, totK_node, atot7180, atot7181]
  decide +kernel

theorem arows7185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7185 = true := by
  rw [show A10K2.u7185 = KTree.node A10K2.u7183 (nat_lit 118662802) (nat_lit 15872022006) (nat_lit 0) A10K2.u7184 from rfl, allE_node, arows7183, irow7185, arows7184]
  all_goals rfl

theorem atot7185 : totK PA10K2 A10K2.u7185 = [0, 0, 1994806613264, 7264906192343, 7655325376833, 2055319330545, 127875982085, 0, 0, 0] := by
  rw [show A10K2.u7185 = KTree.node A10K2.u7183 (nat_lit 118662802) (nat_lit 15872022006) (nat_lit 0) A10K2.u7184 from rfl, totK_node, atot7183, atot7184]
  decide +kernel

theorem arows7189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7189 = true := by
  rw [show A10K2.u7189 = KTree.node A10K2.u7187 (nat_lit 118752042) (nat_lit 8717605911) (nat_lit 0) A10K2.u7188 from rfl, allE_node, arows7187, irow7189, arows7188]
  all_goals rfl

theorem atot7189 : totK PA10K2 A10K2.u7189 = [0, 0, 970705008339, 5147229763878, 8061430390541, 4045782151753, 691954419227, 31725663621, 0, 0] := by
  rw [show A10K2.u7189 = KTree.node A10K2.u7187 (nat_lit 118752042) (nat_lit 8717605911) (nat_lit 0) A10K2.u7188 from rfl, totK_node, atot7187, atot7188]
  decide +kernel

theorem arows7192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7192 = true := by
  rw [show A10K2.u7192 = KTree.node A10K2.u7190 (nat_lit 118770528) (nat_lit 11307087167) (nat_lit 0) A10K2.u7191 from rfl, allE_node, arows7190, irow7192, arows7191]
  all_goals rfl

theorem atot7192 : totK PA10K2 A10K2.u7192 = [0, 0, 1343077793455, 5760370982207, 7982566684907, 3613628930895, 440226746723, 11801668502, 0, 0] := by
  rw [show A10K2.u7192 = KTree.node A10K2.u7190 (nat_lit 118770528) (nat_lit 11307087167) (nat_lit 0) A10K2.u7191 from rfl, totK_node, atot7190, atot7191]
  decide +kernel

theorem arows7198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7198 = true := by
  rw [show A10K2.u7198 = KTree.node A10K2.u7196 (nat_lit 118884898) (nat_lit 8347381410) (nat_lit 0) A10K2.u7197 from rfl, allE_node, arows7196, irow7198, arows7197]
  all_goals rfl

theorem atot7198 : totK PA10K2 A10K2.u7198 = [0, 0, 960273817815, 4719610636222, 8074273765191, 4764287401940, 794044492560, 36928231554, 0, 0] := by
  rw [show A10K2.u7198 = KTree.node A10K2.u7196 (nat_lit 118884898) (nat_lit 8347381410) (nat_lit 0) A10K2.u7197 from rfl, totK_node, atot7196, atot7197]
  decide +kernel

theorem arows7201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7201 = true := by
  rw [show A10K2.u7201 = KTree.node A10K2.u7199 (nat_lit 118899143) (nat_lit 11000919001) (nat_lit 0) A10K2.u7200 from rfl, allE_node, arows7199, irow7201, arows7200]
  all_goals rfl

theorem atot7201 : totK PA10K2 A10K2.u7201 = [0, 0, 1184669949864, 5767251551908, 8224455452777, 3384872249836, 354715628679, 6034215561, 0, 0] := by
  rw [show A10K2.u7201 = KTree.node A10K2.u7199 (nat_lit 118899143) (nat_lit 11000919001) (nat_lit 0) A10K2.u7200 from rfl, totK_node, atot7199, atot7200]
  decide +kernel

theorem arows7205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7205 = true := by
  rw [show A10K2.u7205 = KTree.node A10K2.u7203 (nat_lit 118924628) (nat_lit 12879484709) (nat_lit 0) A10K2.u7204 from rfl, allE_node, arows7203, irow7205, arows7204]
  all_goals rfl

theorem atot7205 : totK PA10K2 A10K2.u7205 = [0, 0, 0, 2327384746400, 7917091941012, 6881395566959, 1456932117582, 74461528785, 0, 0] := by
  rw [show A10K2.u7205 = KTree.node A10K2.u7203 (nat_lit 118924628) (nat_lit 12879484709) (nat_lit 0) A10K2.u7204 from rfl, totK_node, atot7203, atot7204]
  decide +kernel

theorem arows7208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7208 = true := by
  rw [show A10K2.u7208 = KTree.node A10K2.u7206 (nat_lit 119015950) (nat_lit 11762319368) (nat_lit 0) A10K2.u7207 from rfl, allE_node, arows7206, irow7208, arows7207]
  all_goals rfl

theorem atot7208 : totK PA10K2 A10K2.u7208 = [0, 835923233680, 3743102169442, 5634331077234, 4098545708659, 2963762006977, 1366475235241, 195382007035, 6354482628, 0] := by
  rw [show A10K2.u7208 = KTree.node A10K2.u7206 (nat_lit 119015950) (nat_lit 11762319368) (nat_lit 0) A10K2.u7207 from rfl, totK_node, atot7206, atot7207]
  decide +kernel

theorem arows7213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7213 = true := by
  rw [show A10K2.u7213 = KTree.node A10K2.u7211 (nat_lit 119037953) (nat_lit 10590452259) (nat_lit 0) A10K2.u7212 from rfl, allE_node, arows7211, irow7213, arows7212]
  all_goals rfl

theorem atot7213 : totK PA10K2 A10K2.u7213 = [0, 1341052302012, 5856242074050, 8235712879578, 3764905663563, 433374462790, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7213 = KTree.node A10K2.u7211 (nat_lit 119037953) (nat_lit 10590452259) (nat_lit 0) A10K2.u7212 from rfl, totK_node, atot7211, atot7212]
  decide +kernel

theorem arows7216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7216 = true := by
  rw [show A10K2.u7216 = KTree.node A10K2.u7214 (nat_lit 119048354) (nat_lit 4047639967) (nat_lit 0) A10K2.u7215 from rfl, allE_node, arows7214, irow7216, arows7215]
  all_goals rfl

theorem atot7216 : totK PA10K2 A10K2.u7216 = [0, 0, 1360020553270, 5794428190600, 7882944506552, 3670317706360, 611313489788, 30650496230, 0, 0] := by
  rw [show A10K2.u7216 = KTree.node A10K2.u7214 (nat_lit 119048354) (nat_lit 4047639967) (nat_lit 0) A10K2.u7215 from rfl, totK_node, atot7214, atot7215]
  decide +kernel

theorem arows7220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7220 = true := by
  rw [show A10K2.u7220 = KTree.node A10K2.u7218 (nat_lit 119069538) (nat_lit 9694670388) (nat_lit 0) A10K2.u7219 from rfl, allE_node, arows7218, irow7220, arows7219]
  all_goals rfl

theorem atot7220 : totK PA10K2 A10K2.u7220 = [0, 305030648051, 2214706096054, 6266802656408, 7510086822620, 2959147698594, 322633286141, 5546304973, 0, 0] := by
  rw [show A10K2.u7220 = KTree.node A10K2.u7218 (nat_lit 119069538) (nat_lit 9694670388) (nat_lit 0) A10K2.u7219 from rfl, totK_node, atot7218, atot7219]
  decide +kernel

theorem arows7223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7223 = true := by
  rw [show A10K2.u7223 = KTree.node A10K2.u7221 (nat_lit 119093946) (nat_lit 13623871475) (nat_lit 0) A10K2.u7222 from rfl, allE_node, arows7221, irow7223, arows7222]
  all_goals rfl

theorem atot7223 : totK PA10K2 A10K2.u7223 = [0, 1301704932031, 5796355298273, 8439839760484, 4249660916762, 576538840035, 13576218110, 0, 0, 0] := by
  rw [show A10K2.u7223 = KTree.node A10K2.u7221 (nat_lit 119093946) (nat_lit 13623871475) (nat_lit 0) A10K2.u7222 from rfl, totK_node, atot7221, atot7222]
  decide +kernel

theorem arows7230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7230 = true := by
  rw [show A10K2.u7230 = KTree.node A10K2.u7228 (nat_lit 119121586) (nat_lit 15220691742) (nat_lit 0) A10K2.u7229 from rfl, allE_node, arows7228, irow7230, arows7229]
  all_goals rfl

theorem atot7230 : totK PA10K2 A10K2.u7230 = [0, 0, 1603399703856, 6383410158179, 8130158355555, 3523184419530, 481258426193, 13576218110, 0, 0] := by
  rw [show A10K2.u7230 = KTree.node A10K2.u7228 (nat_lit 119121586) (nat_lit 15220691742) (nat_lit 0) A10K2.u7229 from rfl, totK_node, atot7228, atot7229]
  decide +kernel

theorem arows7233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7233 = true := by
  rw [show A10K2.u7233 = KTree.node A10K2.u7231 (nat_lit 119210057) (nat_lit 9594707706) (nat_lit 0) A10K2.u7232 from rfl, allE_node, arows7231, irow7233, arows7232]
  all_goals rfl

theorem atot7233 : totK PA10K2 A10K2.u7233 = [0, 777824669607, 3974017337822, 7429559031474, 5947088011650, 1825323654646, 141625161299, 0, 0, 0] := by
  rw [show A10K2.u7233 = KTree.node A10K2.u7231 (nat_lit 119210057) (nat_lit 9594707706) (nat_lit 0) A10K2.u7232 from rfl, totK_node, atot7231, atot7232]
  decide +kernel

theorem arows7237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7237 = true := by
  rw [show A10K2.u7237 = KTree.node A10K2.u7235 (nat_lit 119222003) (nat_lit 9156035615) (nat_lit 0) A10K2.u7236 from rfl, allE_node, arows7235, irow7237, arows7236]
  all_goals rfl

theorem atot7237 : totK PA10K2 A10K2.u7237 = [0, 1238087173529, 5407318836734, 8068545142632, 4600624590937, 797177643936, 29328593449, 0, 0, 0] := by
  rw [show A10K2.u7237 = KTree.node A10K2.u7235 (nat_lit 119222003) (nat_lit 9156035615) (nat_lit 0) A10K2.u7236 from rfl, totK_node, atot7235, atot7236]
  decide +kernel

theorem arows7240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7240 = true := by
  rw [show A10K2.u7240 = KTree.node A10K2.u7238 (nat_lit 119240639) (nat_lit 14162250694) (nat_lit 0) A10K2.u7239 from rfl, allE_node, arows7238, irow7240, arows7239]
  all_goals rfl

theorem atot7240 : totK PA10K2 A10K2.u7240 = [0, 330854518425, 3184620413724, 7980573141959, 6712779938449, 1655102691083, 94006812352, 0, 0, 0] := by
  rw [show A10K2.u7240 = KTree.node A10K2.u7238 (nat_lit 119240639) (nat_lit 14162250694) (nat_lit 0) A10K2.u7239 from rfl, totK_node, atot7238, atot7239]
  decide +kernel

theorem arows7245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7245 = true := by
  rw [show A10K2.u7245 = KTree.node A10K2.u7243 (nat_lit 119253228) (nat_lit 8920936886) (nat_lit 0) A10K2.u7244 from rfl, allE_node, arows7243, irow7245, arows7244]
  all_goals rfl

theorem atot7245 : totK PA10K2 A10K2.u7245 = [0, 0, 966904360933, 5090108312284, 8545206689083, 4780724765493, 664405157606, 13951953716, 0, 0] := by
  rw [show A10K2.u7245 = KTree.node A10K2.u7243 (nat_lit 119253228) (nat_lit 8920936886) (nat_lit 0) A10K2.u7244 from rfl, totK_node, atot7243, atot7244]
  decide +kernel

theorem arows7248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7248 = true := by
  rw [show A10K2.u7248 = KTree.node A10K2.u7246 (nat_lit 119272674) (nat_lit 13901827180) (nat_lit 0) A10K2.u7247 from rfl, allE_node, arows7246, irow7248, arows7247]
  all_goals rfl

theorem atot7248 : totK PA10K2 A10K2.u7248 = [0, 0, 1139807374609, 5030964883652, 7668112014904, 4743052275826, 1018470278411, 61110126106, 0, 0] := by
  rw [show A10K2.u7248 = KTree.node A10K2.u7246 (nat_lit 119272674) (nat_lit 13901827180) (nat_lit 0) A10K2.u7247 from rfl, totK_node, atot7246, atot7247]
  decide +kernel

theorem arows7252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7252 = true := by
  rw [show A10K2.u7252 = KTree.node A10K2.u7250 (nat_lit 119282871) (nat_lit 14735890773) (nat_lit 0) A10K2.u7251 from rfl, allE_node, arows7250, irow7252, arows7251]
  all_goals rfl

theorem atot7252 : totK PA10K2 A10K2.u7252 = [0, 0, 858510272731, 4553513711452, 7963174211773, 4678194307509, 826776747922, 36485460093, 0, 0] := by
  rw [show A10K2.u7252 = KTree.node A10K2.u7250 (nat_lit 119282871) (nat_lit 14735890773) (nat_lit 0) A10K2.u7251 from rfl, totK_node, atot7250, atot7251]
  decide +kernel

theorem arows7255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7255 = true := by
  rw [show A10K2.u7255 = KTree.node A10K2.u7253 (nat_lit 119304741) (nat_lit 6168893101) (nat_lit 0) A10K2.u7254 from rfl, allE_node, arows7253, irow7255, arows7254]
  all_goals rfl

theorem atot7255 : totK PA10K2 A10K2.u7255 = [0, 0, 778443190292, 4224556251418, 7858284026231, 5836200855609, 1442630926796, 87926673087, 0, 0] := by
  rw [show A10K2.u7255 = KTree.node A10K2.u7253 (nat_lit 119304741) (nat_lit 6168893101) (nat_lit 0) A10K2.u7254 from rfl, totK_node, atot7253, atot7254]
  decide +kernel

theorem arows7261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7261 = true := by
  rw [show A10K2.u7261 = KTree.node A10K2.u7259 (nat_lit 119324720) (nat_lit 15015627018) (nat_lit 0) A10K2.u7260 from rfl, allE_node, arows7259, irow7261, arows7260]
  all_goals rfl

theorem atot7261 : totK PA10K2 A10K2.u7261 = [0, 0, 0, 1602053802207, 6474339594573, 7930186043630, 2951142273142, 332624234137, 7007974415, 0] := by
  rw [show A10K2.u7261 = KTree.node A10K2.u7259 (nat_lit 119324720) (nat_lit 15015627018) (nat_lit 0) A10K2.u7260 from rfl, totK_node, atot7259, atot7260]
  decide +kernel

theorem arows7264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7264 = true := by
  rw [show A10K2.u7264 = KTree.node A10K2.u7262 (nat_lit 119353278) (nat_lit 16355011105) (nat_lit 0) A10K2.u7263 from rfl, allE_node, arows7262, irow7264, arows7263]
  all_goals rfl

theorem atot7264 : totK PA10K2 A10K2.u7264 = [0, 0, 1284111989839, 5374016631443, 7810545337447, 4737374048227, 1059583324036, 64001908758, 0, 0] := by
  rw [show A10K2.u7264 = KTree.node A10K2.u7262 (nat_lit 119353278) (nat_lit 16355011105) (nat_lit 0) A10K2.u7263 from rfl, totK_node, atot7262, atot7263]
  decide +kernel

theorem arows7268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7268 = true := by
  rw [show A10K2.u7268 = KTree.node A10K2.u7266 (nat_lit 119373022) (nat_lit 11410772216) (nat_lit 0) A10K2.u7267 from rfl, allE_node, arows7266, irow7268, arows7267]
  all_goals rfl

theorem atot7268 : totK PA10K2 A10K2.u7268 = [0, 0, 320625971501, 3023574466694, 7857575378034, 7156444776956, 1917598513281, 110513089609, 0, 0] := by
  rw [show A10K2.u7268 = KTree.node A10K2.u7266 (nat_lit 119373022) (nat_lit 11410772216) (nat_lit 0) A10K2.u7267 from rfl, totK_node, atot7266, atot7267]
  decide +kernel

theorem arows7271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7271 = true := by
  rw [show A10K2.u7271 = KTree.node A10K2.u7269 (nat_lit 119401718) (nat_lit 16440311496) (nat_lit 0) A10K2.u7270 from rfl, allE_node, arows7269, irow7271, arows7270]
  all_goals rfl

theorem atot7271 : totK PA10K2 A10K2.u7271 = [0, 0, 777824669607, 3667104281665, 6708799819605, 6178312753345, 2432283204080, 282189853656, 7151180950, 0] := by
  rw [show A10K2.u7271 = KTree.node A10K2.u7269 (nat_lit 119401718) (nat_lit 16440311496) (nat_lit 0) A10K2.u7270 from rfl, totK_node, atot7269, atot7270]
  decide +kernel

theorem arows7276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7276 = true := by
  rw [show A10K2.u7276 = KTree.node A10K2.u7274 (nat_lit 119483450) (nat_lit 11890106066) (nat_lit 0) A10K2.u7275 from rfl, allE_node, arows7274, irow7276, arows7275]
  all_goals rfl

theorem atot7276 : totK PA10K2 A10K2.u7276 = [0, 0, 967099744895, 4820142604873, 8200862295295, 5169796044002, 879181316021, 24210880922, 0, 0] := by
  rw [show A10K2.u7276 = KTree.node A10K2.u7274 (nat_lit 119483450) (nat_lit 11890106066) (nat_lit 0) A10K2.u7275 from rfl, totK_node, atot7274, atot7275]
  decide +kernel

theorem arows7279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7279 = true := by
  rw [show A10K2.u7279 = KTree.node A10K2.u7277 (nat_lit 119501992) (nat_lit 958612840) (nat_lit 0) A10K2.u7278 from rfl, allE_node, arows7277, irow7279, arows7278]
  all_goals rfl

theorem atot7279 : totK PA10K2 A10K2.u7279 = [0, 0, 600351679897, 3760519453530, 7874995479421, 6170657897360, 1437353972135, 74831038383, 0, 0] := by
  rw [show A10K2.u7279 = KTree.node A10K2.u7277 (nat_lit 119501992) (nat_lit 958612840) (nat_lit 0) A10K2.u7278 from rfl, totK_node, atot7277, atot7278]
  decide +kernel

theorem arows7283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7283 = true := by
  rw [show A10K2.u7283 = KTree.node A10K2.u7281 (nat_lit 119514811) (nat_lit 7122795149) (nat_lit 0) A10K2.u7282 from rfl, allE_node, arows7281, irow7283, arows7282]
  all_goals rfl

theorem atot7283 : totK PA10K2 A10K2.u7283 = [0, 0, 0, 1128584539701, 5428307033109, 8439641263335, 4370206929964, 562023865101, 12758098799, 0] := by
  rw [show A10K2.u7283 = KTree.node A10K2.u7281 (nat_lit 119514811) (nat_lit 7122795149) (nat_lit 0) A10K2.u7282 from rfl, totK_node, atot7281, atot7282]
  decide +kernel

theorem arows7286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7286 = true := by
  rw [show A10K2.u7286 = KTree.node A10K2.u7284 (nat_lit 119534151) (nat_lit 9878456066) (nat_lit 0) A10K2.u7285 from rfl, allE_node, arows7284, irow7286, arows7285]
  all_goals rfl

theorem atot7286 : totK PA10K2 A10K2.u7286 = [0, 0, 428122261071, 2103421488178, 5059062601260, 6812995096876, 4302188292268, 983297972169, 61018386929, 0] := by
  rw [show A10K2.u7286 = KTree.node A10K2.u7284 (nat_lit 119534151) (nat_lit 9878456066) (nat_lit 0) A10K2.u7285 from rfl, totK_node, atot7284, atot7285]
  decide +kernel

theorem arows7294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7294 = true := by
  rw [show A10K2.u7294 = KTree.node A10K2.u7292 (nat_lit 119544357) (nat_lit 7149674874) (nat_lit 0) A10K2.u7293 from rfl, allE_node, arows7292, irow7294, arows7293]
  all_goals rfl

theorem atot7294 : totK PA10K2 A10K2.u7294 = [0, 0, 1123846211630, 5259560499094, 7815129431323, 4008871957116, 662814942523, 30831673886, 0, 0] := by
  rw [show A10K2.u7294 = KTree.node A10K2.u7292 (nat_lit 119544357) (nat_lit 7149674874) (nat_lit 0) A10K2.u7293 from rfl, totK_node, atot7292, atot7293]
  decide +kernel

theorem arows7297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7297 = true := by
  rw [show A10K2.u7297 = KTree.node A10K2.u7295 (nat_lit 119565718) (nat_lit 16090923929) (nat_lit 0) A10K2.u7296 from rfl, allE_node, arows7295, irow7297, arows7296]
  all_goals rfl

theorem atot7297 : totK PA10K2 A10K2.u7297 = [0, 0, 787080240479, 4282203472232, 7943333581380, 5473134773292, 1167494135263, 53752926527, 0, 0] := by
  rw [show A10K2.u7297 = KTree.node A10K2.u7295 (nat_lit 119565718) (nat_lit 16090923929) (nat_lit 0) A10K2.u7296 from rfl, totK_node, atot7295, atot7296]
  decide +kernel

theorem arows7301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7301 = true := by
  rw [show A10K2.u7301 = KTree.node A10K2.u7299 (nat_lit 119575025) (nat_lit 8743197912) (nat_lit 0) A10K2.u7300 from rfl, allE_node, arows7299, irow7301, arows7300]
  all_goals rfl

theorem atot7301 : totK PA10K2 A10K2.u7301 = [0, 0, 0, 1311991652636, 5669120812349, 7692193522756, 3606753905871, 612255532765, 30650496230, 0] := by
  rw [show A10K2.u7301 = KTree.node A10K2.u7299 (nat_lit 119575025) (nat_lit 8743197912) (nat_lit 0) A10K2.u7300 from rfl, totK_node, atot7299, atot7300]
  decide +kernel

theorem arows7304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7304 = true := by
  rw [show A10K2.u7304 = KTree.node A10K2.u7302 (nat_lit 119596442) (nat_lit 13031919166) (nat_lit 0) A10K2.u7303 from rfl, allE_node, arows7302, irow7304, arows7303]
  all_goals rfl

theorem atot7304 : totK PA10K2 A10K2.u7304 = [0, 0, 576996404534, 3045053189435, 6415344974191, 6325839038827, 2370341418620, 260915577548, 5546304973, 0] := by
  rw [show A10K2.u7304 = KTree.node A10K2.u7302 (nat_lit 119596442) (nat_lit 13031919166) (nat_lit 0) A10K2.u7303 from rfl, totK_node, atot7302, atot7303]
  decide +kernel

theorem arows7309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7309 = true := by
  rw [show A10K2.u7309 = KTree.node A10K2.u7307 (nat_lit 119679239) (nat_lit 3842636366) (nat_lit 0) A10K2.u7308 from rfl, allE_node, arows7307, irow7309, arows7308]
  all_goals rfl

theorem atot7309 : totK PA10K2 A10K2.u7309 = [0, 0, 1212789096669, 5175265843198, 7640590171120, 4332868552406, 745412161023, 36865889447, 0, 0] := by
  rw [show A10K2.u7309 = KTree.node A10K2.u7307 (nat_lit 119679239) (nat_lit 3842636366) (nat_lit 0) A10K2.u7308 from rfl, totK_node, atot7307, atot7308]
  decide +kernel

theorem arows7312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7312 = true := by
  rw [show A10K2.u7312 = KTree.node A10K2.u7310 (nat_lit 119703717) (nat_lit 7321820484) (nat_lit 0) A10K2.u7311 from rfl, allE_node, arows7310, irow7312, arows7311]
  all_goals rfl

theorem atot7312 : totK PA10K2 A10K2.u7312 = [0, 0, 0, 2504337441751, 8019180409042, 6919735053870, 1430335119546, 76226106848, 0, 0] := by
  rw [show A10K2.u7312 = KTree.node A10K2.u7310 (nat_lit 119703717) (nat_lit 7321820484) (nat_lit 0) A10K2.u7311 from rfl, totK_node, atot7310, atot7311]
  decide +kernel

theorem arows7316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7316 = true := by
  rw [show A10K2.u7316 = KTree.node A10K2.u7314 (nat_lit 119734829) (nat_lit 5482939639) (nat_lit 0) A10K2.u7315 from rfl, allE_node, arows7314, irow7316, arows7315]
  all_goals rfl

theorem atot7316 : totK PA10K2 A10K2.u7316 = [0, 0, 810484086859, 3705068129776, 6649746978346, 5735576896016, 1932707252390, 224789723487, 5976421810, 0] := by
  rw [show A10K2.u7316 = KTree.node A10K2.u7314 (nat_lit 119734829) (nat_lit 5482939639) (nat_lit 0) A10K2.u7315 from rfl, totK_node, atot7314, atot7315]
  decide +kernel

theorem arows7319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7319 = true := by
  rw [show A10K2.u7319 = KTree.node A10K2.u7317 (nat_lit 119749691) (nat_lit 5915896995) (nat_lit 0) A10K2.u7318 from rfl, allE_node, arows7317, irow7319, arows7318]
  all_goals rfl

theorem atot7319 : totK PA10K2 A10K2.u7319 = [0, 0, 1358053751487, 5869609931046, 8405962040489, 4175608617565, 546353222140, 12840446565, 0, 0] := by
  rw [show A10K2.u7319 = KTree.node A10K2.u7317 (nat_lit 119749691) (nat_lit 5915896995) (nat_lit 0) A10K2.u7318 from rfl, totK_node, atot7317, atot7318]
  decide +kernel

theorem arows7325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7325 = true := by
  rw [show A10K2.u7325 = KTree.node A10K2.u7323 (nat_lit 119767557) (nat_lit 6324276604) (nat_lit 0) A10K2.u7324 from rfl, allE_node, arows7323, irow7325, arows7324]
  all_goals rfl

theorem atot7325 : totK PA10K2 A10K2.u7325 = [0, 0, 0, 1653281143545, 6545719460970, 8059382546511, 3213655911970, 358940901605, 6904928264, 0] := by
  rw [show A10K2.u7325 = KTree.node A10K2.u7323 (nat_lit 119767557) (nat_lit 6324276604) (nat_lit 0) A10K2.u7324 from rfl, totK_node, atot7323, atot7324]
  decide +kernel

theorem arows7328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7328 = true := by
  rw [show A10K2.u7328 = KTree.node A10K2.u7326 (nat_lit 119792859) (nat_lit 9266525360) (nat_lit 0) A10K2.u7327 from rfl, allE_node, arows7326, irow7328, arows7327]
  all_goals rfl

theorem atot7328 : totK PA10K2 A10K2.u7328 = [0, 0, 0, 1356218001019, 6072987587115, 8428767974884, 3870197432018, 420421332492, 6066958478, 0] := by
  rw [show A10K2.u7328 = KTree.node A10K2.u7326 (nat_lit 119792859) (nat_lit 9266525360) (nat_lit 0) A10K2.u7327 from rfl, totK_node, atot7326, atot7327]
  decide +kernel

theorem arows7332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7332 = true := by
  rw [show A10K2.u7332 = KTree.node A10K2.u7330 (nat_lit 119803794) (nat_lit 11876737204) (nat_lit 0) A10K2.u7331 from rfl, allE_node, arows7330, irow7332, arows7331]
  all_goals rfl

theorem atot7332 : totK PA10K2 A10K2.u7332 = [0, 0, 0, 1155065740925, 4995822207265, 7576533144428, 4496772147389, 987619549972, 59335263784, 0] := by
  rw [show A10K2.u7332 = KTree.node A10K2.u7330 (nat_lit 119803794) (nat_lit 11876737204) (nat_lit 0) A10K2.u7331 from rfl, totK_node, atot7330, atot7331]
  decide +kernel

theorem arows7335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7335 = true := by
  rw [show A10K2.u7335 = KTree.node A10K2.u7333 (nat_lit 119824749) (nat_lit 6209883063) (nat_lit 0) A10K2.u7334 from rfl, allE_node, arows7333, irow7335, arows7334]
  all_goals rfl

theorem atot7335 : totK PA10K2 A10K2.u7335 = [0, 0, 0, 1166873169845, 5451722181351, 8077883377661, 3840574603653, 523594355753, 12558367923, 0] := by
  rw [show A10K2.u7335 = KTree.node A10K2.u7333 (nat_lit 119824749) (nat_lit 6209883063) (nat_lit 0) A10K2.u7334 from rfl, totK_node, atot7333, atot7334]
  decide +kernel

theorem arows7340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7340 = true := by
  rw [show A10K2.u7340 = KTree.node A10K2.u7338 (nat_lit 119836225) (nat_lit 10295722848) (nat_lit 0) A10K2.u7339 from rfl, allE_node, arows7338, irow7340, arows7339]
  all_goals rfl

theorem atot7340 : totK PA10K2 A10K2.u7340 = [0, 0, 0, 0, 1566924090945, 6304728981589, 7660552841527, 3079745901222, 383958472776, 7903172220] := by
  rw [show A10K2.u7340 = KTree.node A10K2.u7338 (nat_lit 119836225) (nat_lit 10295722848) (nat_lit 0) A10K2.u7339 from rfl, totK_node, atot7338, atot7339]
  decide +kernel

theorem arows7343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7343 = true := by
  rw [show A10K2.u7343 = KTree.node A10K2.u7341 (nat_lit 119931382) (nat_lit 16086020248) (nat_lit 0) A10K2.u7342 from rfl, allE_node, arows7341, irow7343, arows7342]
  all_goals rfl

theorem atot7343 : totK PA10K2 A10K2.u7343 = [0, 0, 0, 789704378163, 4336289673684, 7922751942579, 5104806672602, 995199900201, 49819481475, 0] := by
  rw [show A10K2.u7343 = KTree.node A10K2.u7341 (nat_lit 119931382) (nat_lit 16086020248) (nat_lit 0) A10K2.u7342 from rfl, totK_node, atot7341, atot7342]
  decide +kernel

theorem arows7347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7347 = true := by
  rw [show A10K2.u7347 = KTree.node A10K2.u7345 (nat_lit 119949490) (nat_lit 8558226027) (nat_lit 0) A10K2.u7346 from rfl, allE_node, arows7345, irow7347, arows7346]
  all_goals rfl

theorem atot7347 : totK PA10K2 A10K2.u7347 = [0, 0, 0, 1342507666495, 5749988640519, 7951116818518, 3377300181772, 403222202993, 11814975521, 0] := by
  rw [show A10K2.u7347 = KTree.node A10K2.u7345 (nat_lit 119949490) (nat_lit 8558226027) (nat_lit 0) A10K2.u7346 from rfl, totK_node, atot7345, atot7346]
  decide +kernel

theorem arows7350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7350 = true := by
  rw [show A10K2.u7350 = KTree.node A10K2.u7348 (nat_lit 120004031) (nat_lit 14297797703) (nat_lit 0) A10K2.u7349 from rfl, allE_node, arows7348, irow7350, arows7349]
  all_goals rfl

theorem atot7350 : totK PA10K2 A10K2.u7350 = [0, 0, 0, 1630936190704, 6405956433349, 8092616265218, 3498859994568, 441690224251, 13360781053, 0] := by
  rw [show A10K2.u7350 = KTree.node A10K2.u7348 (nat_lit 120004031) (nat_lit 14297797703) (nat_lit 0) A10K2.u7349 from rfl, totK_node, atot7348, atot7349]
  decide +kernel

theorem arows7357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7357 = true := by
  rw [show A10K2.u7357 = KTree.node A10K2.u7355 (nat_lit 120586517) (nat_lit 6640078033) (nat_lit 0) A10K2.u7356 from rfl, allE_node, arows7355, irow7357, arows7356]
  all_goals rfl

theorem atot7357 : totK PA10K2 A10K2.u7357 = [0, 0, 838792425063, 3554441882929, 5938977722724, 5599774601504, 3095156232732, 647760628227, 35503361870, 0] := by
  rw [show A10K2.u7357 = KTree.node A10K2.u7355 (nat_lit 120586517) (nat_lit 6640078033) (nat_lit 0) A10K2.u7356 from rfl, totK_node, atot7355, atot7356]
  decide +kernel

theorem arows7360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7360 = true := by
  rw [show A10K2.u7360 = KTree.node A10K2.u7358 (nat_lit 120604832) (nat_lit 8996602234) (nat_lit 0) A10K2.u7359 from rfl, allE_node, arows7358, irow7360, arows7359]
  all_goals rfl

theorem atot7360 : totK PA10K2 A10K2.u7360 = [0, 0, 1046709195442, 5056412215555, 7972672007804, 4243972794906, 635653094606, 22240312271, 0, 0] := by
  rw [show A10K2.u7360 = KTree.node A10K2.u7358 (nat_lit 120604832) (nat_lit 8996602234) (nat_lit 0) A10K2.u7359 from rfl, totK_node, atot7358, atot7359]
  decide +kernel

theorem arows7364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7364 = true := by
  rw [show A10K2.u7364 = KTree.node A10K2.u7362 (nat_lit 120619521) (nat_lit 10582213929) (nat_lit 0) A10K2.u7363 from rfl, allE_node, arows7362, irow7364, arows7363]
  all_goals rfl

theorem atot7364 : totK PA10K2 A10K2.u7364 = [0, 0, 295757175837, 2968916948959, 8003358825525, 6993451994288, 1506583108117, 76474489653, 0, 0] := by
  rw [show A10K2.u7364 = KTree.node A10K2.u7362 (nat_lit 120619521) (nat_lit 10582213929) (nat_lit 0) A10K2.u7363 from rfl, totK_node, atot7362, atot7363]
  decide +kernel

theorem arows7367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7367 = true := by
  rw [show A10K2.u7367 = KTree.node A10K2.u7365 (nat_lit 120644366) (nat_lit 6830769461) (nat_lit 128) A10K2.u7366 from rfl, allE_node, arows7365, irow7367, arows7366]
  all_goals rfl

theorem atot7367 : totK PA10K2 A10K2.u7367 = [0, 0, 762344704339, 3766914755401, 6901919976550, 5767146121854, 1814209037160, 206102663612, 5546304973, 0] := by
  rw [show A10K2.u7367 = KTree.node A10K2.u7365 (nat_lit 120644366) (nat_lit 6830769461) (nat_lit 128) A10K2.u7366 from rfl, totK_node, atot7365, atot7366]
  decide +kernel

theorem arows7372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7372 = true := by
  rw [show A10K2.u7372 = KTree.node A10K2.u7370 (nat_lit 120727828) (nat_lit 13248933502) (nat_lit 0) A10K2.u7371 from rfl, allE_node, arows7370, irow7372, arows7371]
  all_goals rfl

theorem atot7372 : totK PA10K2 A10K2.u7372 = [0, 0, 937615500030, 4517861961742, 7723710556512, 4916397763204, 874558090699, 42259512619, 0, 0] := by
  rw [show A10K2.u7372 = KTree.node A10K2.u7370 (nat_lit 120727828) (nat_lit 13248933502) (nat_lit 0) A10K2.u7371 from rfl, totK_node, atot7370, atot7371]
  decide +kernel

theorem arows7375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7375 = true := by
  rw [show A10K2.u7375 = KTree.node A10K2.u7373 (nat_lit 120740617) (nat_lit 8159784399) (nat_lit 0) A10K2.u7374 from rfl, allE_node, arows7373, irow7375, arows7374]
  all_goals rfl

theorem atot7375 : totK PA10K2 A10K2.u7375 = [0, 0, 431985945682, 3572137275597, 8065821444402, 5896339646415, 1039935693498, 43869152019, 0, 0] := by
  rw [show A10K2.u7375 = KTree.node A10K2.u7373 (nat_lit 120740617) (nat_lit 8159784399) (nat_lit 0) A10K2.u7374 from rfl, totK_node, atot7373, atot7374]
  decide +kernel

theorem arows7379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7379 = true := by
  rw [show A10K2.u7379 = KTree.node A10K2.u7377 (nat_lit 120769280) (nat_lit 13829741916) (nat_lit 0) A10K2.u7378 from rfl, allE_node, arows7377, irow7379, arows7378]
  all_goals rfl

theorem atot7379 : totK PA10K2 A10K2.u7379 = [0, 0, 540022072669, 2803617693205, 6309603455662, 6588059264180, 2233493639576, 252234373415, 6354482628, 0] := by
  rw [show A10K2.u7379 = KTree.node A10K2.u7377 (nat_lit 120769280) (nat_lit 13829741916) (nat_lit 0) A10K2.u7378 from rfl, totK_node, atot7377, atot7378]
  decide +kernel

theorem arows7382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7382 = true := by
  rw [show A10K2.u7382 = KTree.node A10K2.u7380 (nat_lit 121117796) (nat_lit 11152859462) (nat_lit 0) A10K2.u7381 from rfl, allE_node, arows7380, irow7382, arows7381]
  all_goals rfl

theorem atot7382 : totK PA10K2 A10K2.u7382 = [0, 0, 832108099441, 4602785618549, 8037637967219, 4666652811172, 825024930006, 36808095696, 0, 0] := by
  rw [show A10K2.u7382 = KTree.node A10K2.u7380 (nat_lit 121117796) (nat_lit 11152859462) (nat_lit 0) A10K2.u7381 from rfl, totK_node, atot7380, atot7381]
  decide +kernel

theorem arows7388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7388 = true := by
  rw [show A10K2.u7388 = KTree.node A10K2.u7386 (nat_lit 121139725) (nat_lit 5460887206) (nat_lit 0) A10K2.u7387 from rfl, allE_node, arows7386, irow7388, arows7387]
  all_goals rfl

theorem atot7388 : totK PA10K2 A10K2.u7388 = [0, 0, 793449030898, 4260876635354, 7843506751307, 5848402901786, 1448375099281, 88375597180, 0, 0] := by
  rw [show A10K2.u7388 = KTree.node A10K2.u7386 (nat_lit 121139725) (nat_lit 5460887206) (nat_lit 0) A10K2.u7387 from rfl, totK_node, atot7386, atot7387]
  decide +kernel

theorem arows7391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7391 = true := by
  rw [show A10K2.u7391 = KTree.node A10K2.u7389 (nat_lit 121150650) (nat_lit 12226550756) (nat_lit 0) A10K2.u7390 from rfl, allE_node, arows7389, irow7391, arows7390]
  all_goals rfl

theorem atot7391 : totK PA10K2 A10K2.u7391 = [0, 0, 0, 1420155911791, 6034065416174, 7890884310995, 3405137462417, 479709382865, 13364899180, 0] := by
  rw [show A10K2.u7391 = KTree.node A10K2.u7389 (nat_lit 121150650) (nat_lit 12226550756) (nat_lit 0) A10K2.u7390 from rfl, totK_node, atot7389, atot7390]
  decide +kernel

theorem arows7395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7395 = true := by
  rw [show A10K2.u7395 = KTree.node A10K2.u7393 (nat_lit 121187835) (nat_lit 6239094582) (nat_lit 0) A10K2.u7394 from rfl, allE_node, arows7393, irow7395, arows7394]
  all_goals rfl

theorem atot7395 : totK PA10K2 A10K2.u7395 = [0, 0, 1110912898166, 5064852531037, 7900159060759, 5034669263587, 1181132121168, 70846717828, 0, 0] := by
  rw [show A10K2.u7395 = KTree.node A10K2.u7393 (nat_lit 121187835) (nat_lit 6239094582) (nat_lit 0) A10K2.u7394 from rfl, totK_node, atot7393, atot7394]
  decide +kernel

theorem arows7398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7398 = true := by
  rw [show A10K2.u7398 = KTree.node A10K2.u7396 (nat_lit 121206707) (nat_lit 9536696515) (nat_lit 0) A10K2.u7397 from rfl, allE_node, arows7396, irow7398, arows7397]
  all_goals rfl

theorem atot7398 : totK PA10K2 A10K2.u7398 = [0, 0, 480625918787, 3539544503199, 8041072373069, 6728763084572, 1656785900272, 83190284463, 0, 0] := by
  rw [show A10K2.u7398 = KTree.node A10K2.u7396 (nat_lit 121206707) (nat_lit 9536696515) (nat_lit 0) A10K2.u7397 from rfl, totK_node, atot7396, atot7397]
  decide +kernel

theorem arows7403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7403 = true := by
  rw [show A10K2.u7403 = KTree.node A10K2.u7401 (nat_lit 121236551) (nat_lit 11210411356) (nat_lit 0) A10K2.u7402 from rfl, allE_node, arows7401, irow7403, arows7402]
  all_goals rfl

theorem atot7403 : totK PA10K2 A10K2.u7403 = [0, 0, 777824669607, 3494231363606, 6528052696895, 6301145682452, 2636840777867, 307077888047, 7380853412, 0] := by
  rw [show A10K2.u7403 = KTree.node A10K2.u7401 (nat_lit 121236551) (nat_lit 11210411356) (nat_lit 0) A10K2.u7402 from rfl, totK_node, atot7401, atot7402]
  decide +kernel

theorem arows7406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7406 = true := by
  rw [show A10K2.u7406 = KTree.node A10K2.u7404 (nat_lit 121317527) (nat_lit 12087012632) (nat_lit 0) A10K2.u7405 from rfl, allE_node, arows7404, irow7406, arows7405]
  all_goals rfl

theorem atot7406 : totK PA10K2 A10K2.u7406 = [0, 0, 853663630241, 4609689693783, 8295756611866, 5322224870793, 929166919086, 31121498125, 0, 0] := by
  rw [show A10K2.u7406 = KTree.node A10K2.u7404 (nat_lit 121317527) (nat_lit 12087012632) (nat_lit 0) A10K2.u7405 from rfl, totK_node, atot7404, atot7405]
  decide +kernel

theorem arows7410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7410 = true := by
  rw [show A10K2.u7410 = KTree.node A10K2.u7408 (nat_lit 121336378) (nat_lit 9874823010) (nat_lit 0) A10K2.u7409 from rfl, allE_node, arows7408, irow7410, arows7409]
  all_goals rfl

theorem atot7410 : totK PA10K2 A10K2.u7410 = [0, 0, 715278061713, 4084264660052, 7874727834563, 5853589742633, 1432620754006, 81490929768, 0, 0] := by
  rw [show A10K2.u7410 = KTree.node A10K2.u7408 (nat_lit 121336378) (nat_lit 9874823010) (nat_lit 0) A10K2.u7409 from rfl, totK_node, atot7408, atot7409]
  decide +kernel

theorem arows7413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7413 = true := by
  rw [show A10K2.u7413 = KTree.node A10K2.u7411 (nat_lit 121349332) (nat_lit 11468875979) (nat_lit 0) A10K2.u7412 from rfl, allE_node, arows7411, irow7413, arows7412]
  all_goals rfl

theorem atot7413 : totK PA10K2 A10K2.u7413 = [0, 0, 0, 1059383755668, 5458109530709, 8467883860413, 4371215141034, 561697113765, 13671283666, 0] := by
  rw [show A10K2.u7413 = KTree.node A10K2.u7411 (nat_lit 121349332) (nat_lit 11468875979) (nat_lit 0) A10K2.u7412 from rfl, totK_node, atot7411, atot7412]
  decide +kernel

theorem arows7422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7422 = true := by
  rw [show A10K2.u7422 = KTree.node A10K2.u7420 (nat_lit 121368649) (nat_lit 8552232890) (nat_lit 0) A10K2.u7421 from rfl, allE_node, arows7420, irow7422, arows7421]
  all_goals rfl

theorem atot7422 : totK PA10K2 A10K2.u7422 = [0, 322245181260, 977713555127, 1604119933964, 4279265882105, 6949179769913, 4635693746220, 1029741685652, 61110126106, 0] := by
  rw [show A10K2.u7422 = KTree.node A10K2.u7420 (nat_lit 121368649) (nat_lit 8552232890) (nat_lit 0) A10K2.u7421 from rfl, totK_node, atot7420, atot7421]
  decide +kernel

theorem arows7425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7425 = true := by
  rw [show A10K2.u7425 = KTree.node A10K2.u7423 (nat_lit 122238988) (nat_lit 11161548178) (nat_lit 0) A10K2.u7424 from rfl, allE_node, arows7423, irow7425, arows7424]
  all_goals rfl

theorem atot7425 : totK PA10K2 A10K2.u7425 = [0, 1233621111224, 5270558598815, 7653603375708, 4200768681554, 707548499577, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7425 = KTree.node A10K2.u7423 (nat_lit 122238988) (nat_lit 11161548178) (nat_lit 0) A10K2.u7424 from rfl, totK_node, atot7423, atot7424]
  decide +kernel

theorem arows7429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7429 = true := by
  rw [show A10K2.u7429 = KTree.node A10K2.u7427 (nat_lit 122250995) (nat_lit 8437989451) (nat_lit 0) A10K2.u7428 from rfl, allE_node, arows7427, irow7429, arows7428]
  all_goals rfl

theorem atot7429 : totK PA10K2 A10K2.u7429 = [0, 788312884667, 4665803110148, 8465555087927, 4994265554684, 773458598988, 20087051677, 0, 0, 0] := by
  rw [show A10K2.u7429 = KTree.node A10K2.u7427 (nat_lit 122250995) (nat_lit 8437989451) (nat_lit 0) A10K2.u7428 from rfl, totK_node, atot7427, atot7428]
  decide +kernel

theorem arows7432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7432 = true := by
  rw [show A10K2.u7432 = KTree.node A10K2.u7430 (nat_lit 122269580) (nat_lit 2529219737) (nat_lit 0) A10K2.u7431 from rfl, allE_node, arows7430, irow7432, arows7431]
  all_goals rfl

theorem atot7432 : totK PA10K2 A10K2.u7432 = [0, 0, 1249891504593, 5445319496748, 7792093298727, 3948457452207, 658735934404, 31082886609, 0, 0] := by
  rw [show A10K2.u7432 = KTree.node A10K2.u7430 (nat_lit 122269580) (nat_lit 2529219737) (nat_lit 0) A10K2.u7431 from rfl, totK_node, atot7430, atot7431]
  decide +kernel

theorem arows7437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7437 = true := by
  rw [show A10K2.u7437 = KTree.node A10K2.u7435 (nat_lit 122282437) (nat_lit 1270818458) (nat_lit 0) A10K2.u7436 from rfl, allE_node, arows7435, irow7437, arows7436]
  all_goals rfl

theorem atot7437 : totK PA10K2 A10K2.u7437 = [0, 251986720587, 2057837983467, 6041836726039, 7326063516057, 3026862501038, 328844540295, 6121173289, 0, 0] := by
  rw [show A10K2.u7437 = KTree.node A10K2.u7435 (nat_lit 122282437) (nat_lit 1270818458) (nat_lit 0) A10K2.u7436 from rfl, totK_node, atot7435, atot7436]
  decide +kernel

theorem arows7440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7440 = true := by
  rw [show A10K2.u7440 = KTree.node A10K2.u7438 (nat_lit 122302430) (nat_lit 14780398333) (nat_lit 0) A10K2.u7439 from rfl, allE_node, arows7438, irow7440, arows7439]
  all_goals rfl

theorem atot7440 : totK PA10K2 A10K2.u7440 = [0, 1197772652057, 5084423031186, 7628466398936, 4547460908280, 838010361016, 37229241746, 0, 0, 0] := by
  rw [show A10K2.u7440 = KTree.node A10K2.u7438 (nat_lit 122302430) (nat_lit 14780398333) (nat_lit 0) A10K2.u7439 from rfl, totK_node, atot7438, atot7439]
  decide +kernel

theorem arows7444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7444 = true := by
  rw [show A10K2.u7444 = KTree.node A10K2.u7442 (nat_lit 122325037) (nat_lit 6533873830) (nat_lit 0) A10K2.u7443 from rfl, allE_node, arows7442, irow7444, arows7443]
  all_goals rfl

theorem atot7444 : totK PA10K2 A10K2.u7444 = [0, 334417811759, 3334318857156, 7895413493148, 6135289964439, 1306263426356, 52053363644, 0, 0, 0] := by
  rw [show A10K2.u7444 = KTree.node A10K2.u7442 (nat_lit 122325037) (nat_lit 6533873830) (nat_lit 0) A10K2.u7443 from rfl, totK_node, atot7442, atot7443]
  decide +kernel

theorem arows7447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7447 = true := by
  rw [show A10K2.u7447 = KTree.node A10K2.u7445 (nat_lit 122345659) (nat_lit 5431975818) (nat_lit 0) A10K2.u7446 from rfl, allE_node, arows7445, irow7447, arows7446]
  all_goals rfl

theorem atot7447 : totK PA10K2 A10K2.u7447 = [0, 511028321977, 3049628708775, 6919257368788, 6576901134848, 2194863500925, 241006205302, 6354482628, 0, 0] := by
  rw [show A10K2.u7447 = KTree.node A10K2.u7445 (nat_lit 122345659) (nat_lit 5431975818) (nat_lit 0) A10K2.u7446 from rfl, totK_node, atot7445, atot7446]
  decide +kernel

theorem arows7453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7453 = true := by
  rw [show A10K2.u7453 = KTree.node A10K2.u7451 (nat_lit 122369431) (nat_lit 14237883125) (nat_lit 0) A10K2.u7452 from rfl, allE_node, arows7451, irow7453, arows7452]
  all_goals rfl

theorem atot7453 : totK PA10K2 A10K2.u7453 = [0, 1335701642573, 5650542054503, 8007035444957, 4234278373579, 722097632657, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u7453 = KTree.node A10K2.u7451 (nat_lit 122369431) (nat_lit 14237883125) (nat_lit 0) A10K2.u7452 from rfl, totK_node, atot7451, atot7452]
  decide +kernel

theorem arows7456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7456 = true := by
  rw [show A10K2.u7456 = KTree.node A10K2.u7454 (nat_lit 122387866) (nat_lit 14487834767) (nat_lit 0) A10K2.u7455 from rfl, allE_node, arows7454, irow7456, arows7455]
  all_goals rfl

theorem atot7456 : totK PA10K2 A10K2.u7456 = [0, 323706995196, 2655959446525, 7015491242567, 7316336160581, 2778536301062, 308447811351, 6904928264, 0, 0] := by
  rw [show A10K2.u7456 = KTree.node A10K2.u7454 (nat_lit 122387866) (nat_lit 14487834767) (nat_lit 0) A10K2.u7455 from rfl, totK_node, atot7454, atot7455]
  decide +kernel

theorem arows7460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7460 = true := by
  rw [show A10K2.u7460 = KTree.node A10K2.u7458 (nat_lit 122402117) (nat_lit 5796855975) (nat_lit 0) A10K2.u7459 from rfl, allE_node, arows7458, irow7460, arows7459]
  all_goals rfl

theorem atot7460 : totK PA10K2 A10K2.u7460 = [0, 0, 1485006819936, 6144449618339, 8131830726365, 3696668608708, 433806357786, 7047025452, 0, 0] := by
  rw [show A10K2.u7460 = KTree.node A10K2.u7458 (nat_lit 122402117) (nat_lit 5796855975) (nat_lit 0) A10K2.u7459 from rfl, totK_node, atot7458, atot7459]
  decide +kernel

theorem arows7463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7463 = true := by
  rw [show A10K2.u7463 = KTree.node A10K2.u7461 (nat_lit 122420922) (nat_lit 14266321332) (nat_lit 0) A10K2.u7462 from rfl, allE_node, arows7461, irow7463, arows7462]
  all_goals rfl

theorem atot7463 : totK PA10K2 A10K2.u7463 = [0, 0, 1043297552052, 4950185518857, 7841621511625, 4842360775414, 1040623880227, 61110126106, 0, 0] := by
  rw [show A10K2.u7463 = KTree.node A10K2.u7461 (nat_lit 122420922) (nat_lit 14266321332) (nat_lit 0) A10K2.u7462 from rfl, totK_node, atot7461, atot7462]
  decide +kernel

theorem arows7468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7468 = true := by
  rw [show A10K2.u7468 = KTree.node A10K2.u7466 (nat_lit 122504862) (nat_lit 13891866505) (nat_lit 0) A10K2.u7467 from rfl, allE_node, arows7466, irow7468, arows7467]
  all_goals rfl

theorem atot7468 : totK PA10K2 A10K2.u7468 = [0, 0, 860370224915, 4505802366570, 7788961474900, 4676834487217, 832241911620, 38008422587, 0, 0] := by
  rw [show A10K2.u7468 = KTree.node A10K2.u7466 (nat_lit 122504862) (nat_lit 13891866505) (nat_lit 0) A10K2.u7467 from rfl, totK_node, atot7466, atot7467]
  decide +kernel

theorem arows7471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7471 = true := by
  rw [show A10K2.u7471 = KTree.node A10K2.u7469 (nat_lit 122517154) (nat_lit 14286667535) (nat_lit 0) A10K2.u7470 from rfl, allE_node, arows7469, irow7471, arows7470]
  all_goals rfl

theorem atot7471 : totK PA10K2 A10K2.u7471 = [0, 0, 609977757965, 3768982244954, 7853262503192, 6103307431798, 1425085901985, 73586045739, 0, 0] := by
  rw [show A10K2.u7471 = KTree.node A10K2.u7469 (nat_lit 122517154) (nat_lit 14286667535) (nat_lit 0) A10K2.u7470 from rfl, totK_node, atot7469, atot7470]
  decide +kernel

theorem arows7475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7475 = true := by
  rw [show A10K2.u7475 = KTree.node A10K2.u7473 (nat_lit 122536293) (nat_lit 7278552219) (nat_lit 0) A10K2.u7474 from rfl, allE_node, arows7473, irow7475, arows7474]
  all_goals rfl

theorem atot7475 : totK PA10K2 A10K2.u7475 = [0, 0, 0, 899174385219, 4873842401889, 7936062256268, 4075125187699, 664929325088, 31018567651, 0] := by
  rw [show A10K2.u7475 = KTree.node A10K2.u7473 (nat_lit 122536293) (nat_lit 7278552219) (nat_lit 0) A10K2.u7474 from rfl, totK_node, atot7473, atot7474]
  decide +kernel

theorem arows7478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7478 = true := by
  rw [show A10K2.u7478 = KTree.node A10K2.u7476 (nat_lit 122558472) (nat_lit 14333013362) (nat_lit 0) A10K2.u7477 from rfl, allE_node, arows7476, irow7478, arows7477]
  all_goals rfl

theorem atot7478 : totK PA10K2 A10K2.u7478 = [0, 0, 1050022894405, 4863316564935, 7502169940567, 4581917895191, 1294075062336, 179031489639, 5685526223, 0] := by
  rw [show A10K2.u7478 = KTree.node A10K2.u7476 (nat_lit 122558472) (nat_lit 14333013362) (nat_lit 0) A10K2.u7477 from rfl, totK_node, atot7476, atot7477]
  decide +kernel

theorem arows7485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7485 = true := by
  rw [show A10K2.u7485 = KTree.node A10K2.u7483 (nat_lit 122570196) (nat_lit 9205761599) (nat_lit 0) A10K2.u7484 from rfl, allE_node, arows7483, irow7485, arows7484]
  all_goals rfl

theorem atot7485 : totK PA10K2 A10K2.u7485 = [0, 0, 743454972142, 4341462614086, 7963627715007, 4960700204942, 865615528928, 38123231481, 0, 0] := by
  rw [show A10K2.u7485 = KTree.node A10K2.u7483 (nat_lit 122570196) (nat_lit 9205761599) (nat_lit 0) A10K2.u7484 from rfl, totK_node, atot7483, atot7484]
  decide +kernel

theorem arows7488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7488 = true := by
  rw [show A10K2.u7488 = KTree.node A10K2.u7486 (nat_lit 122601741) (nat_lit 5899193217) (nat_lit 0) A10K2.u7487 from rfl, allE_node, arows7486, irow7488, arows7487]
  all_goals rfl

theorem atot7488 : totK PA10K2 A10K2.u7488 = [0, 0, 0, 1664730138504, 6898529611526, 7933793707001, 2200872176327, 140616518484, 0, 0] := by
  rw [show A10K2.u7488 = KTree.node A10K2.u7486 (nat_lit 122601741) (nat_lit 5899193217) (nat_lit 0) A10K2.u7487 from rfl, totK_node, atot7486, atot7487]
  decide +kernel

theorem arows7492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7492 = true := by
  rw [show A10K2.u7492 = KTree.node A10K2.u7490 (nat_lit 122627227) (nat_lit 10068108498) (nat_lit 0) A10K2.u7491 from rfl, allE_node, arows7490, irow7492, arows7491]
  all_goals rfl

theorem atot7492 : totK PA10K2 A10K2.u7492 = [0, 0, 1321139709677, 5670234853374, 7915826031707, 4138922050706, 976283149688, 138218344971, 6239673734, 0] := by
  rw [show A10K2.u7492 = KTree.node A10K2.u7490 (nat_lit 122627227) (nat_lit 10068108498) (nat_lit 0) A10K2.u7491 from rfl, totK_node, atot7490, atot7491]
  decide +kernel

theorem arows7495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7495 = true := by
  rw [show A10K2.u7495 = KTree.node A10K2.u7493 (nat_lit 122645549) (nat_lit 864350096) (nat_lit 0) A10K2.u7494 from rfl, allE_node, arows7493, irow7495, arows7494]
  all_goals rfl

theorem atot7495 : totK PA10K2 A10K2.u7495 = [0, 0, 845271374385, 4451936948384, 8078052278841, 5483705260933, 1090682889776, 44529605603, 0, 0] := by
  rw [show A10K2.u7495 = KTree.node A10K2.u7493 (nat_lit 122645549) (nat_lit 864350096) (nat_lit 0) A10K2.u7494 from rfl, totK_node, atot7493, atot7494]
  decide +kernel

theorem arows7500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7500 = true := by
  rw [show A10K2.u7500 = KTree.node A10K2.u7498 (nat_lit 122761171) (nat_lit 9231652012) (nat_lit 0) A10K2.u7499 from rfl, allE_node, arows7498, irow7500, arows7499]
  all_goals rfl

theorem atot7500 : totK PA10K2 A10K2.u7500 = [0, 1189372542830, 4930858346820, 7064975257808, 4169716075313, 1453920785327, 490072389596, 49137922124, 0, 0] := by
  rw [show A10K2.u7500 = KTree.node A10K2.u7498 (nat_lit 122761171) (nat_lit 9231652012) (nat_lit 0) A10K2.u7499 from rfl, totK_node, atot7498, atot7499]
  decide +kernel

theorem arows7503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7503 = true := by
  rw [show A10K2.u7503 = KTree.node A10K2.u7501 (nat_lit 122772307) (nat_lit 8504819587) (nat_lit 0) A10K2.u7502 from rfl, allE_node, arows7501, irow7503, arows7502]
  all_goals rfl

theorem atot7503 : totK PA10K2 A10K2.u7503 = [0, 998607669562, 5178566287982, 8365029526288, 4479016371188, 641795324511, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u7503 = KTree.node A10K2.u7501 (nat_lit 122772307) (nat_lit 8504819587) (nat_lit 0) A10K2.u7502 from rfl, totK_node, atot7501, atot7502]
  decide +kernel

theorem arows7507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7507 = true := by
  rw [show A10K2.u7507 = KTree.node A10K2.u7505 (nat_lit 122793876) (nat_lit 8113384784) (nat_lit 0) A10K2.u7506 from rfl, allE_node, arows7505, irow7507, arows7506]
  all_goals rfl

theorem atot7507 : totK PA10K2 A10K2.u7507 = [0, 0, 1269082589719, 5610016482920, 7858118023295, 3877623253963, 641565463625, 31082886609, 0, 0] := by
  rw [show A10K2.u7507 = KTree.node A10K2.u7505 (nat_lit 122793876) (nat_lit 8113384784) (nat_lit 0) A10K2.u7506 from rfl, totK_node, atot7505, atot7506]
  decide +kernel

theorem arows7510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7510 = true := by
  rw [show A10K2.u7510 = KTree.node A10K2.u7508 (nat_lit 122807533) (nat_lit 5466146321) (nat_lit 0) A10K2.u7509 from rfl, allE_node, arows7508, irow7510, arows7509]
  all_goals rfl

theorem atot7510 : totK PA10K2 A10K2.u7510 = [0, 561156172308, 2771769438456, 6066515639583, 6858043173498, 2823353724988, 291564873131, 6121173289, 0, 0] := by
  rw [show A10K2.u7510 = KTree.node A10K2.u7508 (nat_lit 122807533) (nat_lit 5466146321) (nat_lit 0) A10K2.u7509 from rfl, totK_node, atot7508, atot7509]
  decide +kernel

theorem arows7516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7516 = true := by
  rw [show A10K2.u7516 = KTree.node A10K2.u7514 (nat_lit 122824895) (nat_lit 10574095452) (nat_lit 0) A10K2.u7515 from rfl, allE_node, arows7514, irow7516, arows7515]
  all_goals rfl

theorem atot7516 : totK PA10K2 A10K2.u7516 = [0, 767148028666, 4269217966224, 7843118829446, 5157086532956, 1053089005129, 62600422739, 0, 0, 0] := by
  rw [show A10K2.u7516 = KTree.node A10K2.u7514 (nat_lit 122824895) (nat_lit 10574095452) (nat_lit 0) A10K2.u7515 from rfl, totK_node, atot7514, atot7515]
  decide +kernel

theorem arows7519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7519 = true := by
  rw [show A10K2.u7519 = KTree.node A10K2.u7517 (nat_lit 122835304) (nat_lit 9842299144) (nat_lit 0) A10K2.u7518 from rfl, allE_node, arows7517, irow7519, arows7518]
  all_goals rfl

theorem atot7519 : totK PA10K2 A10K2.u7519 = [0, 820824437048, 4455384557281, 7863671805342, 4929570582928, 884684394312, 38342359577, 0, 0, 0] := by
  rw [show A10K2.u7519 = KTree.node A10K2.u7517 (nat_lit 122835304) (nat_lit 9842299144) (nat_lit 0) A10K2.u7518 from rfl, totK_node, atot7517, atot7518]
  decide +kernel

theorem arows7523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7523 = true := by
  rw [show A10K2.u7523 = KTree.node A10K2.u7521 (nat_lit 122864518) (nat_lit 10368367537) (nat_lit 0) A10K2.u7522 from rfl, allE_node, arows7521, irow7523, arows7522]
  all_goals rfl

theorem atot7523 : totK PA10K2 A10K2.u7523 = [0, 0, 1554280243312, 6546058710120, 8022725793466, 2628821686510, 207975276816, 0, 0, 0] := by
  rw [show A10K2.u7523 = KTree.node A10K2.u7521 (nat_lit 122864518) (nat_lit 10368367537) (nat_lit 0) A10K2.u7522 from rfl, totK_node, atot7521, atot7522]
  decide +kernel

theorem arows7526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7526 = true := by
  rw [show A10K2.u7526 = KTree.node A10K2.u7524 (nat_lit 123024609) (nat_lit 3858250514) (nat_lit 0) A10K2.u7525 from rfl, allE_node, arows7524, irow7526, arows7525]
  all_goals rfl

theorem atot7526 : totK PA10K2 A10K2.u7526 = [0, 0, 1303479160595, 5400181604669, 7548940209820, 4142540937729, 777546088610, 37807056478, 0, 0] := by
  rw [show A10K2.u7526 = KTree.node A10K2.u7524 (nat_lit 123024609) (nat_lit 3858250514) (nat_lit 0) A10K2.u7525 from rfl, totK_node, atot7524, atot7525]
  decide +kernel

theorem arows7531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7531 = true := by
  rw [show A10K2.u7531 = KTree.node A10K2.u7529 (nat_lit 123037062) (nat_lit 15451681561) (nat_lit 0) A10K2.u7530 from rfl, allE_node, arows7529, irow7531, arows7530]
  all_goals rfl

theorem atot7531 : totK PA10K2 A10K2.u7531 = [0, 0, 1056704560129, 5140362377869, 8342459561816, 4458692156394, 586992831340, 13317224979, 0, 0] := by
  rw [show A10K2.u7531 = KTree.node A10K2.u7529 (nat_lit 123037062) (nat_lit 15451681561) (nat_lit 0) A10K2.u7530 from rfl, totK_node, atot7529, atot7530]
  decide +kernel

theorem arows7534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7534 = true := by
  rw [show A10K2.u7534 = KTree.node A10K2.u7532 (nat_lit 123086267) (nat_lit 7059444141) (nat_lit 0) A10K2.u7533 from rfl, allE_node, arows7532, irow7534, arows7533]
  all_goals rfl

theorem atot7534 : totK PA10K2 A10K2.u7534 = [0, 0, 1155101996528, 5475756621875, 8080765897043, 3807278496389, 564854826604, 30429722018, 0, 0] := by
  rw [show A10K2.u7534 = KTree.node A10K2.u7532 (nat_lit 123086267) (nat_lit 7059444141) (nat_lit 0) A10K2.u7533 from rfl, totK_node, atot7532, atot7533]
  decide +kernel

theorem arows7538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7538 = true := by
  rw [show A10K2.u7538 = KTree.node A10K2.u7536 (nat_lit 123095600) (nat_lit 13504605493) (nat_lit 0) A10K2.u7537 from rfl, allE_node, arows7536, irow7538, arows7537]
  all_goals rfl

theorem atot7538 : totK PA10K2 A10K2.u7538 = [0, 0, 819213633141, 4525811070740, 8047549165275, 4652702218574, 707228134778, 17774690686, 0, 0] := by
  rw [show A10K2.u7538 = KTree.node A10K2.u7536 (nat_lit 123095600) (nat_lit 13504605493) (nat_lit 0) A10K2.u7537 from rfl, totK_node, atot7536, atot7537]
  decide +kernel

theorem arows7541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7541 = true := by
  rw [show A10K2.u7541 = KTree.node A10K2.u7539 (nat_lit 123126562) (nat_lit 11045330773) (nat_lit 0) A10K2.u7540 from rfl, allE_node, arows7539, irow7541, arows7540]
  all_goals rfl

theorem atot7541 : totK PA10K2 A10K2.u7541 = [0, 0, 0, 1665316853540, 6812605123943, 7705090432870, 2205716117803, 150967543301, 0, 0] := by
  rw [show A10K2.u7541 = KTree.node A10K2.u7539 (nat_lit 123126562) (nat_lit 11045330773) (nat_lit 0) A10K2.u7540 from rfl, totK_node, atot7539, atot7540]
  decide +kernel

theorem arows7549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7549 = true := by
  rw [show A10K2.u7549 = KTree.node A10K2.u7547 (nat_lit 123212225) (nat_lit 10304842917) (nat_lit 0) A10K2.u7548 from rfl, allE_node, arows7547, irow7549, arows7548]
  all_goals rfl

theorem atot7549 : totK PA10K2 A10K2.u7549 = [0, 1409826252325, 5767212448049, 7768716122373, 3722994819793, 764427057452, 433267206025, 136682872893, 6354482628, 0] := by
  rw [show A10K2.u7549 = KTree.node A10K2.u7547 (nat_lit 123212225) (nat_lit 10304842917) (nat_lit 0) A10K2.u7548 from rfl, totK_node, atot7547, atot7548]
  decide +kernel

theorem arows7552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7552 = true := by
  rw [show A10K2.u7552 = KTree.node A10K2.u7550 (nat_lit 123240155) (nat_lit 5957672823) (nat_lit 0) A10K2.u7551 from rfl, allE_node, arows7550, irow7552, arows7551]
  all_goals rfl

theorem atot7552 : totK PA10K2 A10K2.u7552 = [0, 177435414779, 2487253990837, 7403266177851, 7658742902188, 2369885524665, 181692860101, 0, 0, 0] := by
  rw [show A10K2.u7552 = KTree.node A10K2.u7550 (nat_lit 123240155) (nat_lit 5957672823) (nat_lit 0) A10K2.u7551 from rfl, totK_node, atot7550, atot7551]
  decide +kernel

theorem arows7556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7556 = true := by
  rw [show A10K2.u7556 = KTree.node A10K2.u7554 (nat_lit 123268545) (nat_lit 9937805989) (nat_lit 0) A10K2.u7555 from rfl, allE_node, arows7554, irow7556, arows7555]
  all_goals rfl

theorem atot7556 : totK PA10K2 A10K2.u7556 = [0, 838891203471, 3802556568999, 6577614871371, 5779406006258, 2501301865180, 404355875443, 13364899180, 0, 0] := by
  rw [show A10K2.u7556 = KTree.node A10K2.u7554 (nat_lit 123268545) (nat_lit 9937805989) (nat_lit 0) A10K2.u7555 from rfl, totK_node, atot7554, atot7555]
  decide +kernel

theorem arows7559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7559 = true := by
  rw [show A10K2.u7559 = KTree.node A10K2.u7557 (nat_lit 123291412) (nat_lit 13049808624) (nat_lit 0) A10K2.u7558 from rfl, allE_node, arows7557, irow7559, arows7558]
  all_goals rfl

theorem atot7559 : totK PA10K2 A10K2.u7559 = [0, 1024751672328, 4837747228745, 7831416830166, 4716351205744, 854317031066, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u7559 = KTree.node A10K2.u7557 (nat_lit 123291412) (nat_lit 13049808624) (nat_lit 0) A10K2.u7558 from rfl, totK_node, atot7557, atot7558]
  decide +kernel

theorem arows7564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7564 = true := by
  rw [show A10K2.u7564 = KTree.node A10K2.u7562 (nat_lit 123305074) (nat_lit 11735382191) (nat_lit 0) A10K2.u7563 from rfl, allE_node, arows7562, irow7564, arows7563]
  all_goals rfl

theorem atot7564 : totK PA10K2 A10K2.u7564 = [0, 319364795913, 3209284950967, 8008178957592, 6720654402384, 1657872137188, 95502021083, 0, 0, 0] := by
  rw [show A10K2.u7564 = KTree.node A10K2.u7562 (nat_lit 123305074) (nat_lit 11735382191) (nat_lit 0) A10K2.u7563 from rfl, totK_node, atot7562, atot7563]
  decide +kernel

theorem arows7567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7567 = true := by
  rw [show A10K2.u7567 = KTree.node A10K2.u7565 (nat_lit 123324076) (nat_lit 11831981296) (nat_lit 0) A10K2.u7566 from rfl, allE_node, arows7565, irow7567, arows7566]
  all_goals rfl

theorem atot7567 : totK PA10K2 A10K2.u7567 = [0, 0, 911001217776, 4760484139582, 7985140819981, 4571308606141, 800973942089, 37204059898, 0, 0] := by
  rw [show A10K2.u7567 = KTree.node A10K2.u7565 (nat_lit 123324076) (nat_lit 11831981296) (nat_lit 0) A10K2.u7566 from rfl, totK_node, atot7565, atot7566]
  decide +kernel

theorem arows7571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7571 = true := by
  rw [show A10K2.u7571 = KTree.node A10K2.u7569 (nat_lit 123407748) (nat_lit 7860618035) (nat_lit 0) A10K2.u7570 from rfl, allE_node, arows7569, irow7571, arows7570]
  all_goals rfl

theorem atot7571 : totK PA10K2 A10K2.u7571 = [0, 985345008910, 4622239480833, 7710863873843, 5380341821211, 1390784392991, 94700245651, 0, 0, 0] := by
  rw [show A10K2.u7571 = KTree.node A10K2.u7569 (nat_lit 123407748) (nat_lit 7860618035) (nat_lit 0) A10K2.u7570 from rfl, totK_node, atot7569, atot7570]
  decide +kernel

theorem arows7574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7574 = true := by
  rw [show A10K2.u7574 = KTree.node A10K2.u7572 (nat_lit 123419490) (nat_lit 11477959185) (nat_lit 0) A10K2.u7573 from rfl, allE_node, arows7572, irow7574, arows7573]
  all_goals rfl

theorem atot7574 : totK PA10K2 A10K2.u7574 = [0, 1361858516948, 5773868345389, 8033786612777, 4041303634128, 657243377177, 31677228370, 0, 0, 0] := by
  rw [show A10K2.u7574 = KTree.node A10K2.u7572 (nat_lit 123419490) (nat_lit 11477959185) (nat_lit 0) A10K2.u7573 from rfl, totK_node, atot7572, atot7573]
  decide +kernel

theorem arows7580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7580 = true := by
  rw [show A10K2.u7580 = KTree.node A10K2.u7578 (nat_lit 123437175) (nat_lit 14322157986) (nat_lit 0) A10K2.u7579 from rfl, allE_node, arows7578, irow7580, arows7579]
  all_goals rfl

theorem atot7580 : totK PA10K2 A10K2.u7580 = [0, 0, 1683887341381, 6667696944183, 8206496653364, 3247499628777, 343362861351, 6904928264, 0, 0] := by
  rw [show A10K2.u7580 = KTree.node A10K2.u7578 (nat_lit 123437175) (nat_lit 14322157986) (nat_lit 0) A10K2.u7579 from rfl, totK_node, atot7578, atot7579]
  decide +kernel

theorem arows7583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7583 = true := by
  rw [show A10K2.u7583 = KTree.node A10K2.u7581 (nat_lit 123450772) (nat_lit 8891622075) (nat_lit 0) A10K2.u7582 from rfl, allE_node, arows7581, irow7583, arows7582]
  all_goals rfl

theorem atot7583 : totK PA10K2 A10K2.u7583 = [0, 0, 1488503252292, 6136426491987, 8094092184539, 3664477116277, 428251624826, 7047025452, 0, 0] := by
  rw [show A10K2.u7583 = KTree.node A10K2.u7581 (nat_lit 123450772) (nat_lit 8891622075) (nat_lit 0) A10K2.u7582 from rfl, totK_node, atot7581, atot7582]
  decide +kernel

theorem arows7587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7587 = true := by
  rw [show A10K2.u7587 = KTree.node A10K2.u7585 (nat_lit 123469431) (nat_lit 14468159826) (nat_lit 0) A10K2.u7586 from rfl, allE_node, arows7585, irow7587, arows7586]
  all_goals rfl

theorem atot7587 : totK PA10K2 A10K2.u7587 = [0, 0, 941997919994, 4786252803315, 7973787495389, 5076079869268, 1071418910894, 61110126106, 0, 0] := by
  rw [show A10K2.u7587 = KTree.node A10K2.u7585 (nat_lit 123469431) (nat_lit 14468159826) (nat_lit 0) A10K2.u7586 from rfl, totK_node, atot7585, atot7586]
  decide +kernel

theorem arows7590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7590 = true := by
  rw [show A10K2.u7590 = KTree.node A10K2.u7588 (nat_lit 123497544) (nat_lit 13602958860) (nat_lit 0) A10K2.u7589 from rfl, allE_node, arows7588, irow7590, arows7589]
  all_goals rfl

theorem atot7590 : totK PA10K2 A10K2.u7590 = [0, 0, 824587356464, 4393935264555, 8272456647028, 5805387308546, 1102113162884, 32487122911, 0, 0] := by
  rw [show A10K2.u7590 = KTree.node A10K2.u7588 (nat_lit 123497544) (nat_lit 13602958860) (nat_lit 0) A10K2.u7589 from rfl, totK_node, atot7588, atot7589]
  decide +kernel

theorem arows7595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7595 = true := by
  rw [show A10K2.u7595 = KTree.node A10K2.u7593 (nat_lit 123507209) (nat_lit 9781991067) (nat_lit 0) A10K2.u7594 from rfl, allE_node, arows7593, irow7595, arows7594]
  all_goals rfl

theorem atot7595 : totK PA10K2 A10K2.u7595 = [0, 0, 0, 1599461780806, 6622472578621, 8395306620012, 3165385860086, 318544467965, 7007974415, 0] := by
  rw [show A10K2.u7595 = KTree.node A10K2.u7593 (nat_lit 123507209) (nat_lit 9781991067) (nat_lit 0) A10K2.u7594 from rfl, totK_node, atot7593, atot7594]
  decide +kernel

theorem arows7598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7598 = true := by
  rw [show A10K2.u7598 = KTree.node A10K2.u7596 (nat_lit 123548896) (nat_lit 5711083031) (nat_lit 0) A10K2.u7597 from rfl, allE_node, arows7596, irow7598, arows7597]
  all_goals rfl

theorem atot7598 : totK PA10K2 A10K2.u7598 = [0, 0, 1262604785756, 5214645223874, 7468302583926, 4350688822529, 995454412950, 75027878843, 0, 0] := by
  rw [show A10K2.u7598 = KTree.node A10K2.u7596 (nat_lit 123548896) (nat_lit 5711083031) (nat_lit 0) A10K2.u7597 from rfl, totK_node, atot7596, atot7597]
  decide +kernel

theorem arows7602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7602 = true := by
  rw [show A10K2.u7602 = KTree.node A10K2.u7600 (nat_lit 123561824) (nat_lit 3787681361) (nat_lit 0) A10K2.u7601 from rfl, allE_node, arows7600, irow7602, arows7601]
  all_goals rfl

theorem atot7602 : totK PA10K2 A10K2.u7602 = [0, 0, 920402885956, 4953220422857, 8416758529898, 4837828983636, 762745839620, 19482267969, 0, 0] := by
  rw [show A10K2.u7602 = KTree.node A10K2.u7600 (nat_lit 123561824) (nat_lit 3787681361) (nat_lit 0) A10K2.u7601 from rfl, totK_node, atot7600, atot7601]
  decide +kernel

theorem arows7605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7605 = true := by
  rw [show A10K2.u7605 = KTree.node A10K2.u7603 (nat_lit 123580378) (nat_lit 13327874738) (nat_lit 0) A10K2.u7604 from rfl, allE_node, arows7603, irow7605, arows7604]
  all_goals rfl

theorem atot7605 : totK PA10K2 A10K2.u7605 = [0, 0, 0, 1561356235063, 6248485945825, 7869414299928, 3297684312131, 391032460102, 7151180950, 0] := by
  rw [show A10K2.u7605 = KTree.node A10K2.u7603 (nat_lit 123580378) (nat_lit 13327874738) (nat_lit 0) A10K2.u7604 from rfl, totK_node, atot7603, atot7604]
  decide +kernel

end QECKChecks.A10K2
